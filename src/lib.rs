// Copyright 2015 Nicholas Allegra (comex).
// Licensed under the Apache License, Version 2.0 <https://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <https://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
//

//! Based on the [shlex](https://crates.io/crates/shlex), adapted for OsStr/OsString.
//!
//! -------
//!
//! Same idea as (but implementation not directly based on) the Python shlex module.  However, this
//! implementation does not support any of the Python module's customization because it makes
//! parsing slower and is fairly useless.  You only get the default settings of shlex.split, which
//! mimic the POSIX shell:
//! <https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html>
//!
//! This implementation also deviates from the Python version in not treating `\r` specially, which
//! I believe is more compliant.
//!
//! The algorithms in this crate are oblivious to UTF-8 high bytes, so they iterate over the bytes
//! directly as a micro-optimization.
//!
//! Disabling the `std` feature (which is enabled by default) will allow the crate to work in
//! `no_std` environments, where the `alloc` crate, and a global allocator, are available.


use std::borrow::Cow;
use std::ffi::{OsStr, OsString};
use std::vec;

use os_str_bytes::{OsStrBytes, OsStringBytes};
use os_str_bytes::RawOsString;

// TODO: Use `Iterator::join` instead when implemented:
//       https://github.com/rust-lang/rust/issues/75638
struct MultiOsStrJoinerWrapper<'a> {
    inner: Vec<Cow<'a, OsStr>>,
}

impl<'a> MultiOsStrJoinerWrapper<'a> {
    fn into_joined(self, sep: &OsStr) -> OsString {
        if self.inner.is_empty() {
            return OsString::default();
        }

        let capacity = self.inner
            .iter()
            .map(|s| s.len() + sep.len())
            .sum::<usize>() - sep.len();
        let mut ret = OsString::with_capacity(capacity);
        let mut iter = self.inner.into_iter();
        ret.push(iter.next().expect("impossible due to is_empty() check above"));
        iter.for_each(|s| {
            ret.push(sep);
            ret.push(s);
        });
        ret
    }
}

/// An iterator that takes an input string and splits it into the words using the same syntax as
/// the POSIX shell.
pub struct ShlexOs {
    in_iter: vec::IntoIter<u8>,
    /// The number of newlines read so far, plus one.
    pub line_no: usize,
    /// An input string is erroneous if it ends while inside a quotation or right after an
    /// unescaped backslash.  Since Iterator does not have a mechanism to return an error, if that
    /// happens, Shlex just throws out the last token, ends the iteration, and sets 'had_error' to
    /// true; best to check it after you're done iterating.
    pub had_error: bool,
}

impl ShlexOs {
    pub fn new(in_string: impl Into<OsString>) -> Self {
        let raw = RawOsString::new(in_string.into());
        Self {
            in_iter: raw.into_raw_vec().into_iter(),
            line_no: 1,
            had_error: false,
        }
        //Self::_new(raw)
    }

    fn parse_word(&mut self, mut ch: u8) -> Option<OsString> {
        let mut result: Vec<u8> = Vec::new();
        loop {
            match ch {
                b'"' => if let Err(()) = self.parse_double(&mut result) {
                    self.had_error = true;
                    return None;
                },
                b'\'' => if let Err(()) = self.parse_single(&mut result) {
                    self.had_error = true;
                    return None;
                },
                b'\\' => if let Some(ch2) = self.next_char() {
                    if ch2 != b'\n' { result.push(ch2); }
                } else {
                    self.had_error = true;
                    return None;
                },
                b' ' | b'\t' | b'\n' => { break; },
                _ => { result.push(ch); },
            }
            if let Some(ch2) = self.next_char() { ch = ch2; } else { break; }
        }
        Some(OsString::from_raw_vec(result).expect("should never fail"))
    }

    fn parse_double(&mut self, result: &mut Vec<u8>) -> Result<(), ()> {
        loop {
            if let Some(ch2) = self.next_char() {
                match ch2 {
                    b'\\' => {
                        if let Some(ch3) = self.next_char() {
                            match ch3 {
                                // \$ => $
                                b'$' | b'`' | b'"' | b'\\' => { result.push(ch3); },
                                // \<newline> => nothing
                                b'\n' => {},
                                // \x => =x
                                _ => { result.push(b'\\'); result.push(ch3); }
                            }
                        } else {
                            return Err(());
                        }
                    },
                    b'"' => { return Ok(()); },
                    _ => { result.push(ch2); },
                }
            } else {
                return Err(());
            }
        }
    }

    fn parse_single(&mut self, result: &mut Vec<u8>) -> Result<(), ()> {
        loop {
            if let Some(ch2) = self.next_char() {
                match ch2 {
                    b'\'' => { return Ok(()); },
                    _ => { result.push(ch2); },
                }
            } else {
                return Err(());
            }
        }
    }

    fn next_char(&mut self) -> Option<u8> {
        let res = self.in_iter.next();
        if res == Some(b'\n') { self.line_no += 1; }
        res
    }
}

impl Iterator for ShlexOs {
    type Item = OsString;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(mut ch) = self.next_char() {
            // skip initial whitespace
            loop {
                match ch {
                    b' ' | b'\t' | b'\n' => {},
                    b'#' => {
                        while let Some(ch2) = self.next_char() {
                            if ch2 == b'\n' { break; }
                        }
                    },
                    _ => { break; }
                }
                if let Some(ch2) = self.next_char() { ch = ch2; } else { return None; }
            }
            self.parse_word(ch)
        } else { // no initial character
            None
        }
    }

}

/// Convenience function that consumes the whole string at once.  Returns None if the input was
/// erroneous.
pub fn split(in_str: &OsStr) -> Option<Vec<OsString>> {
    let mut shl = ShlexOs::new(in_str);
    let res = shl.by_ref().collect();
    if shl.had_error { None } else { Some(res) }
}

/// Given a single word, return a string suitable to encode it as a shell argument.
pub fn quote(in_str: &OsStr) -> Cow<OsStr> {
    if in_str.len() == 0 {
        OsStr::new("\"\"").into()
    } else if in_str.to_raw_bytes().iter().any(|c| match *c {
        b'|' | b'&' | b';' | b'<' | b'>' | b'(' | b')' | b'$' | b'`' | b'\\' | b'"' | b'\'' | b' ' | b'\t' |
        b'\r' | b'\n' | b'*' | b'?' | b'[' | b'#' | b'~' | b'=' | b'%' => true,
        _ => false
    }) {
        let mut out: Vec<u8> = Vec::new();
        out.push('"' as u8);
        for c in &*in_str.to_raw_bytes() {
            match *c {
                b'$' | b'`' | b'"' | b'\\' => out.push(b'\\'),
                _ => ()
            }
            out.push(*c);
        }
        out.push(b'"');
        OsString::from_raw_vec(out).expect("should never fail").into()
    } else {
        in_str.into()
    }
}

/// Convenience function that consumes an iterable of words and turns it into a single string,
/// quoting words when necessary. Consecutive words will be separated by a single space.
pub fn join<'a, I: IntoIterator<Item = &'a OsStr>>(words: I) -> OsString {
    let vec = words.into_iter()
        .map(quote)
        .collect::<Vec<_>>();
    MultiOsStrJoinerWrapper{ inner: vec }.into_joined(OsStr::new(" "))
}

#[cfg(test)]
static SPLIT_TEST_ITEMS: &'static [(&'static str, Option<&'static [&'static str]>)] = &[
    ("foo$baz", Some(&["foo$baz"])),
    ("foo baz", Some(&["foo", "baz"])),
    ("foo\"bar\"baz", Some(&["foobarbaz"])),
    ("foo \"bar\"baz", Some(&["foo", "barbaz"])),
    ("   foo \nbar", Some(&["foo", "bar"])),
    ("foo\\\nbar", Some(&["foobar"])),
    ("\"foo\\\nbar\"", Some(&["foobar"])),
    ("'baz\\$b'", Some(&["baz\\$b"])),
    ("'baz\\\''", None),
    ("\\", None),
    ("\"\\", None),
    ("'\\", None),
    ("\"", None),
    ("'", None),
    ("foo #bar\nbaz", Some(&["foo", "baz"])),
    ("foo #bar", Some(&["foo"])),
    ("foo#bar", Some(&["foo#bar"])),
    ("foo\"#bar", None),
    ("'\\n'", Some(&["\\n"])),
    ("'\\\\n'", Some(&["\\\\n"])),
];

#[test]
fn test_split() {
    for &(input, output) in SPLIT_TEST_ITEMS {
        assert_eq!(split(input.as_ref()), output.map(|o| o.iter().map(|s| OsStr::new(s).to_os_string()).collect()));
    }
}

#[test]
fn test_lineno() {
    let mut sh = ShlexOs::new(OsStr::new("\nfoo\nbar"));
    while let Some(word) = sh.next() {
        if word == OsStr::new("bar") {
            assert_eq!(sh.line_no, 3);
        }
    }
}

#[test]
fn test_quote() {
    assert_eq!(quote(OsStr::new("foobar")), OsStr::new("foobar"));
    assert_eq!(quote(OsStr::new("foo bar")), OsStr::new("\"foo bar\""));
    assert_eq!(quote(OsStr::new("\"")), OsStr::new("\"\\\"\""));
    assert_eq!(quote(OsStr::new("")), OsStr::new("\"\""));
}

#[test]
fn test_join() {
    assert_eq!(join(vec![]), OsStr::new(""));
    assert_eq!(join(vec![OsStr::new("")]), OsStr::new("\"\""));
    assert_eq!(join(vec![OsStr::new("a"), OsStr::new("b")]), OsStr::new("a b"));
    assert_eq!(join(vec![OsStr::new("foo bar"), OsStr::new("baz")]), OsStr::new("\"foo bar\" baz"));
}
