//! Watcher implementation for Darwin's FSEvents API
//!
//! The FSEvents API provides a mechanism to notify clients about directories they ought to re-scan
//! in order to keep their internal data structures up-to-date with respect to the true state of
//! the file system. (For example, when files or directories are created, modified, or removed.) It
//! sends these notifications "in bulk", possibly notifying the client of changes to several
//! directories in a single callback.
//!
//! For more information see the [FSEvents API reference][ref].
//!
//! TODO: document event translation
//!
//! [ref]: https://developer.apple.com/library/mac/documentation/Darwin/Reference/FSEvents_Ref/

#![allow(non_upper_case_globals, dead_code)]

use crate::event::*;
use crate::{
    unbounded, Config, Error, EventHandler, PathsMut, RecursiveMode, Result, Sender, Watcher,
};
use fsevent_sys as fs;
use fsevent_sys::core_foundation as cf;
use std::collections::HashMap;
use std::ffi::CStr;
use std::fmt;
use std::os::raw;
use std::path::{Path, PathBuf};
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

bitflags::bitflags! {
  #[repr(C)]
  #[derive(Debug)]
  struct StreamFlags: u32 {
    const NONE = fs::kFSEventStreamEventFlagNone;
    const MUST_SCAN_SUBDIRS = fs::kFSEventStreamEventFlagMustScanSubDirs;
    const USER_DROPPED = fs::kFSEventStreamEventFlagUserDropped;
    const KERNEL_DROPPED = fs::kFSEventStreamEventFlagKernelDropped;
    const IDS_WRAPPED = fs::kFSEventStreamEventFlagEventIdsWrapped;
    const HISTORY_DONE = fs::kFSEventStreamEventFlagHistoryDone;
    const ROOT_CHANGED = fs::kFSEventStreamEventFlagRootChanged;
    const MOUNT = fs::kFSEventStreamEventFlagMount;
    const UNMOUNT = fs::kFSEventStreamEventFlagUnmount;
    const ITEM_CREATED = fs::kFSEventStreamEventFlagItemCreated;
    const ITEM_REMOVED = fs::kFSEventStreamEventFlagItemRemoved;
    const INODE_META_MOD = fs::kFSEventStreamEventFlagItemInodeMetaMod;
    const ITEM_RENAMED = fs::kFSEventStreamEventFlagItemRenamed;
    const ITEM_MODIFIED = fs::kFSEventStreamEventFlagItemModified;
    const FINDER_INFO_MOD = fs::kFSEventStreamEventFlagItemFinderInfoMod;
    const ITEM_CHANGE_OWNER = fs::kFSEventStreamEventFlagItemChangeOwner;
    const ITEM_XATTR_MOD = fs::kFSEventStreamEventFlagItemXattrMod;
    const IS_FILE = fs::kFSEventStreamEventFlagItemIsFile;
    const IS_DIR = fs::kFSEventStreamEventFlagItemIsDir;
    const IS_SYMLINK = fs::kFSEventStreamEventFlagItemIsSymlink;
    const OWN_EVENT = fs::kFSEventStreamEventFlagOwnEvent;
    const IS_HARDLINK = fs::kFSEventStreamEventFlagItemIsHardlink;
    const IS_LAST_HARDLINK = fs::kFSEventStreamEventFlagItemIsLastHardlink;
    const ITEM_CLONED = fs::kFSEventStreamEventFlagItemCloned;
  }
}

/// FSEvents-based `Watcher` implementation
pub struct FsEventWatcher {
    paths: cf::CFMutableArrayRef,
    since_when: fs::FSEventStreamEventId,
    latency: cf::CFTimeInterval,
    flags: fs::FSEventStreamCreateFlags,
    event_handler: Arc<Mutex<dyn EventHandler>>,
    runloop: Option<(cf::CFRunLoopRef, Arc<AtomicBool>, thread::JoinHandle<()>)>,
    recursive_info: HashMap<PathBuf, bool>,
}

impl fmt::Debug for FsEventWatcher {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("FsEventWatcher")
            .field("paths", &self.paths)
            .field("since_when", &self.since_when)
            .field("latency", &self.latency)
            .field("flags", &self.flags)
            .field("event_handler", &Arc::as_ptr(&self.event_handler))
            .field("runloop", &self.runloop)
            .field("recursive_info", &self.recursive_info)
            .finish()
    }
}

// CFMutableArrayRef is a type alias to *mut libc::c_void, so FsEventWatcher is not Send/Sync
// automatically. It's Send because the pointer is not used in other threads.
unsafe impl Send for FsEventWatcher {}

// It's Sync because all methods that change the mutable state use `&mut self`.
unsafe impl Sync for FsEventWatcher {}

fn translate_flags(flags: StreamFlags, precise: bool) -> Vec<Event> {
    let mut evs = Vec::new();

    // «Denotes a sentinel event sent to mark the end of the "historical" events
    // sent as a result of specifying a `sinceWhen` value in the FSEvents.Create
    // call that created this event stream. After invoking the client's callback
    // with all the "historical" events that occurred before now, the client's
    // callback will be invoked with an event where the HistoryDone flag is set.
    // The client should ignore the path supplied in this callback.»
    // — https://www.mbsplugins.eu/FSEventsNextEvent.shtml
    //
    // As a result, we just stop processing here and return an empty vec, which
    // will ignore this completely and not emit any Events whatsoever.
    if flags.contains(StreamFlags::HISTORY_DONE) {
        return evs;
    }

    // FSEvents provides two possible hints as to why events were dropped,
    // however documentation on what those mean is scant, so we just pass them
    // through in the info attr field. The intent is clear enough, and the
    // additional information is provided if the user wants it.
    if flags.contains(StreamFlags::MUST_SCAN_SUBDIRS) {
        let e = Event::new(EventKind::Other).set_flag(Flag::Rescan);
        evs.push(if flags.contains(StreamFlags::USER_DROPPED) {
            e.set_info("rescan: user dropped")
        } else if flags.contains(StreamFlags::KERNEL_DROPPED) {
            e.set_info("rescan: kernel dropped")
        } else {
            e
        });
    }

    // In imprecise mode, let's not even bother parsing the kind of the event
    // except for the above very special events.
    if !precise {
        evs.push(Event::new(EventKind::Any));
        return evs;
    }

    // This is most likely a rename or a removal. We assume rename but may want
    // to figure out if it was a removal some way later (TODO). To denote the
    // special nature of the event, we add an info string.
    if flags.contains(StreamFlags::ROOT_CHANGED) {
        evs.push(
            Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::From)))
                .set_info("root changed"),
        );
    }

    // A path was mounted at the event path; we treat that as a create.
    if flags.contains(StreamFlags::MOUNT) {
        evs.push(Event::new(EventKind::Create(CreateKind::Other)).set_info("mount"));
    }

    // A path was unmounted at the event path; we treat that as a remove.
    if flags.contains(StreamFlags::UNMOUNT) {
        evs.push(Event::new(EventKind::Remove(RemoveKind::Other)).set_info("mount"));
    }

    if flags.contains(StreamFlags::ITEM_CREATED) {
        evs.push(if flags.contains(StreamFlags::IS_DIR) {
            Event::new(EventKind::Create(CreateKind::Folder))
        } else if flags.contains(StreamFlags::IS_FILE) {
            Event::new(EventKind::Create(CreateKind::File))
        } else {
            let e = Event::new(EventKind::Create(CreateKind::Other));
            if flags.contains(StreamFlags::IS_SYMLINK) {
                e.set_info("is: symlink")
            } else if flags.contains(StreamFlags::IS_HARDLINK) {
                e.set_info("is: hardlink")
            } else if flags.contains(StreamFlags::ITEM_CLONED) {
                e.set_info("is: clone")
            } else {
                Event::new(EventKind::Create(CreateKind::Any))
            }
        });
    }

    if flags.contains(StreamFlags::ITEM_REMOVED) {
        evs.push(if flags.contains(StreamFlags::IS_DIR) {
            Event::new(EventKind::Remove(RemoveKind::Folder))
        } else if flags.contains(StreamFlags::IS_FILE) {
            Event::new(EventKind::Remove(RemoveKind::File))
        } else {
            let e = Event::new(EventKind::Remove(RemoveKind::Other));
            if flags.contains(StreamFlags::IS_SYMLINK) {
                e.set_info("is: symlink")
            } else if flags.contains(StreamFlags::IS_HARDLINK) {
                e.set_info("is: hardlink")
            } else if flags.contains(StreamFlags::ITEM_CLONED) {
                e.set_info("is: clone")
            } else {
                Event::new(EventKind::Remove(RemoveKind::Any))
            }
        });
    }

    // FSEvents provides no mechanism to associate the old and new sides of a
    // rename event.
    if flags.contains(StreamFlags::ITEM_RENAMED) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Name(
            RenameMode::Any,
        ))));
    }

    // This is only described as "metadata changed", but it may be that it's
    // only emitted for some more precise subset of events... if so, will need
    // amending, but for now we have an Any-shaped bucket to put it in.
    if flags.contains(StreamFlags::INODE_META_MOD) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Any,
        ))));
    }

    if flags.contains(StreamFlags::FINDER_INFO_MOD) {
        evs.push(
            Event::new(EventKind::Modify(ModifyKind::Metadata(MetadataKind::Other)))
                .set_info("meta: finder info"),
        );
    }

    if flags.contains(StreamFlags::ITEM_CHANGE_OWNER) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Ownership,
        ))));
    }

    if flags.contains(StreamFlags::ITEM_XATTR_MOD) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Extended,
        ))));
    }

    // This is specifically described as a data change, which we take to mean
    // is a content change.
    if flags.contains(StreamFlags::ITEM_MODIFIED) {
        evs.push(Event::new(EventKind::Modify(ModifyKind::Data(
            DataChange::Content,
        ))));
    }

    if flags.contains(StreamFlags::OWN_EVENT) {
        for ev in &mut evs {
            *ev = std::mem::take(ev).set_process_id(std::process::id());
        }
    }

    evs
}

struct StreamContextInfo {
    event_handler: Arc<Mutex<dyn EventHandler>>,
    recursive_info: HashMap<PathBuf, bool>,
}

// Free the context when the stream created by `FSEventStreamCreate` is released.
extern "C" fn release_context(info: *const libc::c_void) {
    // Safety:
    // - The [documentation] for `FSEventStreamContext` states that `release` is only
    //   called when the stream is deallocated, so it is safe to convert `info` back into a
    //   box and drop it.
    //
    // [docs]: https://developer.apple.com/documentation/coreservices/fseventstreamcontext?language=objc
    unsafe {
        drop(Box::from_raw(
            info as *const StreamContextInfo as *mut StreamContextInfo,
        ));
    }
}

extern "C" {
    fn CFRunLoopWakeUp(runloop: cf::CFRunLoopRef);
    fn CFRetain(cf: cf::CFRef) -> cf::CFRef;
}

struct FsEventPathsMut<'a>(&'a mut FsEventWatcher);
impl<'a> FsEventPathsMut<'a> {
    fn new(watcher: &'a mut FsEventWatcher) -> Self {
        watcher.stop();
        Self(watcher)
    }
}
impl PathsMut for FsEventPathsMut<'_> {
    fn add(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.0.append_path(path, recursive_mode)
    }

    fn remove(&mut self, path: &Path) -> Result<()> {
        self.0.remove_path(path)
    }

    fn commit(self: Box<Self>) -> Result<()> {
        self.0.run()
    }
}

impl FsEventWatcher {
    fn from_event_handler(event_handler: Arc<Mutex<dyn EventHandler>>) -> Result<Self> {
        Ok(FsEventWatcher {
            paths: unsafe {
                cf::CFArrayCreateMutable(cf::kCFAllocatorDefault, 0, &cf::kCFTypeArrayCallBacks)
            },
            since_when: fs::kFSEventStreamEventIdSinceNow,
            latency: 0.0,
            flags: fs::kFSEventStreamCreateFlagFileEvents
                | fs::kFSEventStreamCreateFlagNoDefer
                | fs::kFSEventStreamCreateFlagWatchRoot,
            event_handler,
            runloop: None,
            recursive_info: HashMap::new(),
        })
    }

    fn watch_inner(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.stop();
        let result = self.append_path(path, recursive_mode);
        self.run()?;
        result
    }

    fn unwatch_inner(&mut self, path: &Path) -> Result<()> {
        self.stop();
        let result = self.remove_path(path);
        self.run()?;
        result
    }

    #[inline]
    fn is_running(&self) -> bool {
        self.runloop.is_some()
    }

    fn stop(&mut self) {
        if !self.is_running() {
            return;
        }

        if let Some((runloop, stop_flag, thread_handle)) = self.runloop.take() {
            unsafe {
                let runloop = runloop as *mut raw::c_void;

                // Don't wait for the runloop to enter the "waiting" state before
                // stopping it: under heavy event load it may never get there, and
                // if the runloop thread already exited (e.g. the stream failed to
                // start) it never will, so waiting would spin forever. The flag
                // makes the thread skip `CFRunLoopRun` if it hasn't entered it yet.
                stop_flag.store(true, Ordering::Release);
                cf::CFRunLoopStop(runloop);
                CFRunLoopWakeUp(runloop);
            }

            // Wait for the thread to shut down.
            thread_handle.join().expect("thread to shut down");

            // Release the retained reference from run().
            unsafe {
                cf::CFRelease(runloop);
            }
        }
    }

    fn remove_path(&mut self, path: &Path) -> Result<()> {
        let str_path = path.to_str().unwrap();
        unsafe {
            let mut err: cf::CFErrorRef = ptr::null_mut();
            let cf_path = cf::str_path_to_cfstring_ref(str_path, &mut err);
            if cf_path.is_null() {
                cf::CFRelease(err as cf::CFRef);
                return Err(Error::watch_not_found().add_path(path.into()));
            }

            let mut to_remove = Vec::new();
            for idx in 0..cf::CFArrayGetCount(self.paths) {
                let item = cf::CFArrayGetValueAtIndex(self.paths, idx);
                if cf::CFStringCompare(item, cf_path, cf::kCFCompareCaseInsensitive)
                    == cf::kCFCompareEqualTo
                {
                    to_remove.push(idx);
                }
            }

            cf::CFRelease(cf_path);

            for idx in to_remove.iter().rev() {
                cf::CFArrayRemoveValueAtIndex(self.paths, *idx);
            }
        }
        let p = if let Ok(canonicalized_path) = path.canonicalize() {
            canonicalized_path
        } else {
            path.to_owned()
        };
        match self.recursive_info.remove(&p) {
            Some(_) => Ok(()),
            None => Err(Error::watch_not_found()),
        }
    }

    // https://github.com/thibaudgg/rb-fsevent/blob/master/ext/fsevent_watch/main.c
    fn append_path(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        if !path.exists() {
            return Err(Error::path_not_found().add_path(path.into()));
        }
        let canonical_path = path.to_path_buf().canonicalize()?;
        let str_path = path.to_str().unwrap();
        unsafe {
            let mut err: cf::CFErrorRef = ptr::null_mut();
            let cf_path = cf::str_path_to_cfstring_ref(str_path, &mut err);
            if cf_path.is_null() {
                // Most likely the directory was deleted, or permissions changed,
                // while the above code was running.
                cf::CFRelease(err as cf::CFRef);
                return Err(Error::path_not_found().add_path(path.into()));
            }
            cf::CFArrayAppendValue(self.paths, cf_path);
            cf::CFRelease(cf_path);
        }
        self.recursive_info
            .insert(canonical_path, recursive_mode.is_recursive());
        Ok(())
    }

    fn run(&mut self) -> Result<()> {
        if unsafe { cf::CFArrayGetCount(self.paths) } == 0 {
            // The watcher is allowed to have no paths (e.g. after unwatching
            // the last one); staying stopped is the correct state.
            return Ok(());
        }

        // We need to associate the stream context with our callback in order to propagate events
        // to the rest of the system. This will be owned by the stream, and will be freed when the
        // stream is closed. This means we will leak the context if we panic before reaching
        // `FSEventStreamRelease`.
        let context = Box::into_raw(Box::new(StreamContextInfo {
            event_handler: self.event_handler.clone(),
            recursive_info: self.recursive_info.clone(),
        }));

        let stream_context = fs::FSEventStreamContext {
            version: 0,
            info: context as *mut libc::c_void,
            retain: None,
            release: Some(release_context),
            copy_description: None,
        };

        let stream = unsafe {
            fs::FSEventStreamCreate(
                cf::kCFAllocatorDefault,
                callback,
                &stream_context,
                self.paths,
                self.since_when,
                self.latency,
                self.flags,
            )
        };

        // Wrapper to help send CFRef types across threads.
        struct CFSendWrapper(cf::CFRef);

        // Safety:
        // - According to the Apple documentation, it's safe to move `CFRef`s across threads.
        //   https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/ThreadSafetySummary/ThreadSafetySummary.html
        unsafe impl Send for CFSendWrapper {}

        // move into thread
        let stream = CFSendWrapper(stream);

        // channel to pass runloop around
        let (rl_tx, rl_rx) = unbounded();

        // Used to stop the runloop thread without relying on
        // `CFRunLoopIsWaiting()` becoming true under heavy event load.
        let stop_flag = Arc::new(AtomicBool::new(false));
        let stop_flag_thread = Arc::clone(&stop_flag);

        let thread_handle = thread::Builder::new()
            .name("notify-rs fsevents loop".to_string())
            .spawn(move || {
                let _ = &stream;
                let stream = stream.0;

                unsafe {
                    let cur_runloop = cf::CFRunLoopGetCurrent();

                    fs::FSEventStreamScheduleWithRunLoop(
                        stream,
                        cur_runloop,
                        cf::kCFRunLoopDefaultMode,
                    );
                    if fs::FSEventStreamStart(stream) == 0 {
                        // Propagate the failure instead of carrying on: if this
                        // thread exited while the caller held a runloop handle,
                        // the next `stop()` would wait forever on a dead runloop.
                        fs::FSEventStreamInvalidate(stream);
                        fs::FSEventStreamRelease(stream);
                        let _ = rl_tx.send(Err(Error::generic("unable to start FSEvent stream")));
                        return;
                    }

                    // Retain the runloop so the reference we send to the
                    // caller survives even if this thread exits before
                    // stop() uses it. The caller releases in stop().
                    CFRetain(cur_runloop);

                    // `stop()` will call `CFRunLoopStop` + `CFRunLoopWakeUp` and
                    // then join this thread.
                    let Ok(_) = rl_tx.send(Ok(CFSendWrapper(cur_runloop))) else {
                        cf::CFRelease(cur_runloop);
                        panic!("Unable to send runloop to watcher");
                    };

                    if !stop_flag_thread.load(Ordering::Acquire) {
                        cf::CFRunLoopRun();
                    }
                    fs::FSEventStreamStop(stream);
                    // There are edge-cases, when many events are pending,
                    // despite the stream being stopped, that the stream's
                    // associated callback will be invoked. Purging events
                    // is intended to prevent this.
                    let event_id = fs::FSEventsGetCurrentEventId();
                    let device = fs::FSEventStreamGetDeviceBeingWatched(stream);
                    fs::FSEventsPurgeEventsForDeviceUpToEventId(device, event_id);
                    fs::FSEventStreamInvalidate(stream);
                    fs::FSEventStreamRelease(stream);
                }
            })?;
        // block until runloop has been sent
        match rl_rx.recv() {
            Ok(Ok(runloop)) => {
                self.runloop = Some((runloop.0, stop_flag, thread_handle));
            }
            Ok(Err(err)) => {
                thread_handle
                    .join()
                    .expect("thread to shut down after FSEvent stream start failure");
                return Err(err);
            }
            Err(_) => {
                thread_handle
                    .join()
                    .expect("thread to shut down after FSEvent stream startup channel close");
                return Err(Error::generic(
                    "unable to receive FSEvent stream startup result",
                ));
            }
        }

        Ok(())
    }

    fn configure_raw_mode(&mut self, _config: Config, tx: Sender<Result<bool>>) {
        tx.send(Ok(false))
            .expect("configuration channel disconnect");
    }
}

extern "C" fn callback(
    stream_ref: fs::FSEventStreamRef,
    info: *mut libc::c_void,
    num_events: libc::size_t,                        // size_t numEvents
    event_paths: *mut libc::c_void,                  // void *eventPaths
    event_flags: *const fs::FSEventStreamEventFlags, // const FSEventStreamEventFlags eventFlags[]
    event_ids: *const fs::FSEventStreamEventId,      // const FSEventStreamEventId eventIds[]
) {
    unsafe {
        callback_impl(
            stream_ref,
            info,
            num_events,
            event_paths,
            event_flags,
            event_ids,
        )
    }
}

unsafe fn callback_impl(
    _stream_ref: fs::FSEventStreamRef,
    info: *mut libc::c_void,
    num_events: libc::size_t,                        // size_t numEvents
    event_paths: *mut libc::c_void,                  // void *eventPaths
    event_flags: *const fs::FSEventStreamEventFlags, // const FSEventStreamEventFlags eventFlags[]
    _event_ids: *const fs::FSEventStreamEventId,     // const FSEventStreamEventId eventIds[]
) {
    let event_paths = event_paths as *const *const libc::c_char;
    let info = info as *const StreamContextInfo;
    let event_handler = &(*info).event_handler;

    for p in 0..num_events {
        let path = CStr::from_ptr(*event_paths.add(p))
            .to_str()
            .expect("Invalid UTF8 string.");
        let path = PathBuf::from(path);

        let flag = *event_flags.add(p);
        let flag = StreamFlags::from_bits(flag).unwrap_or_else(|| {
            panic!("Unable to decode StreamFlags: {}", flag);
        });

        let mut handle_event = false;
        for (p, r) in &(*info).recursive_info {
            if path.starts_with(p) {
                if *r || &path == p {
                    handle_event = true;
                    break;
                } else if let Some(parent_path) = path.parent() {
                    if parent_path == p {
                        handle_event = true;
                        break;
                    }
                }
            }
        }

        if !handle_event {
            continue;
        }

        log::trace!("FSEvent: path = `{}`, flag = {:?}", path.display(), flag);

        for ev in translate_flags(flag, true).into_iter() {
            // TODO: precise
            let ev = ev.add_path(path.clone());
            let mut event_handler = event_handler.lock().expect("lock not to be poisoned");
            event_handler.handle_event(Ok(ev));
        }
    }
}

impl Watcher for FsEventWatcher {
    /// Create a new watcher.
    fn new<F: EventHandler>(event_handler: F, _config: Config) -> Result<Self> {
        Self::from_event_handler(Arc::new(Mutex::new(event_handler)))
    }

    fn watch(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.watch_inner(path, recursive_mode)
    }

    fn paths_mut<'me>(&'me mut self) -> Box<dyn PathsMut + 'me> {
        Box::new(FsEventPathsMut::new(self))
    }

    fn unwatch(&mut self, path: &Path) -> Result<()> {
        self.unwatch_inner(path)
    }

    fn configure(&mut self, config: Config) -> Result<bool> {
        let (tx, rx) = unbounded();
        self.configure_raw_mode(config, tx);
        rx.recv()?
    }

    fn kind() -> crate::WatcherKind {
        crate::WatcherKind::Fsevent
    }
}

impl Drop for FsEventWatcher {
    fn drop(&mut self) {
        self.stop();
        unsafe {
            cf::CFRelease(self.paths);
        }
    }
}

#[test]
fn test_fsevent_watcher_drop() {
    use super::*;
    use std::time::Duration;

    let dir = tempfile::tempdir().unwrap();

    let (tx, rx) = std::sync::mpsc::channel();

    {
        let mut watcher = FsEventWatcher::new(tx, Default::default()).unwrap();
        watcher.watch(dir.path(), RecursiveMode::Recursive).unwrap();
        thread::sleep(Duration::from_millis(2000));
        println!("is running -> {}", watcher.is_running());

        thread::sleep(Duration::from_millis(1000));
        watcher.unwatch(dir.path()).unwrap();
        println!("is running -> {}", watcher.is_running());
    }

    thread::sleep(Duration::from_millis(1000));

    for res in rx {
        let e = res.unwrap();
        println!("debug => {:?} {:?}", e.kind, e.paths);
    }

    println!("in test: {} works", file!());
}

#[test]
fn test_steam_context_info_send_and_sync() {
    fn check_send<T: Send + Sync>() {}
    check_send::<StreamContextInfo>();
}


// fsevents does not allow watching more than 4096 paths in one stream, so
// FSEventStreamStart fails. Regression test for two related shutdown hangs:
// before propagating the start failure, the runloop thread exited silently
// while `self.runloop` was still `Some`, and the next watch/unwatch call spun
// forever in `stop()` waiting for `CFRunLoopIsWaiting()` on a dead runloop.
// https://github.com/fsnotify/fsevents/issues/48
#[test]
fn watcher_does_not_hang_after_stream_start_failure() {
    use std::sync::mpsc;
    use std::time::Duration;

    let tmpdir = tempfile::tempdir().unwrap();
    let mut paths = Vec::new();
    for i in 0..=4096 {
        let path = tmpdir.path().join(format!("dir_{i}"));
        std::fs::create_dir(&path).expect("create_dir");
        paths.push(path);
    }

    let (done_tx, done_rx) = mpsc::channel::<()>();
    let watch_thread = thread::spawn(move || {
        let (tx, _rx) = mpsc::channel();
        let mut watcher = FsEventWatcher::new(tx, Default::default()).unwrap();

        {
            let mut paths_mut = watcher.paths_mut();
            for path in &paths {
                paths_mut
                    .add(path, RecursiveMode::NonRecursive)
                    .expect("add path");
            }
            // The stream fails to start here; the error must be surfaced
            // and the watcher left in a stopped state rather than holding a
            // handle to a dead runloop.
            let commit_error = paths_mut.commit().expect_err("commit should surface start failure");
            assert!(
                commit_error.to_string().contains("unable to start FSEvent stream"),
                "unexpected commit error: {commit_error}"
            );
        }

        // Both of these used to hang forever in `stop()`.
        let extra = tmpdir.path().join("extra");
        std::fs::create_dir(&extra).expect("create_dir");
        watcher
            .watch(&extra, RecursiveMode::NonRecursive)
            .expect_err("watch should surface start failure while over the limit");
        drop(watcher);

        // Bypass `TempDir`'s Drop: `remove_dir_all` can be flaky with this
        // many directories while fsevents may still hold references.
        let tmpdir_path = tmpdir.path().to_path_buf();
        std::mem::forget(tmpdir);
        let _ = std::fs::remove_dir_all(&tmpdir_path);

        let _ = done_tx.send(());
    });

    done_rx
        .recv_timeout(Duration::from_secs(60))
        .expect("watcher operations timed out (possible shutdown hang)");
    watch_thread.join().expect("watch thread to shut down");
}
