-- Prove2me | Theorems.Thm_Poly1305DebianApi_verifyOk_donna_verify
-- name    : Poly1305DebianApi.verifyOk_donna_verify
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T11:24:33.523203+00:00
-- url     : https://prove2.me/theorems/a7b2dfc7-9b6e-4453-b1d2-1392a8b25fb0
-- title:
--   poly1305_donna.c, crypto_onetimeauth_poly1305_donna_verify — returns 0 if the tag is RFC 8439's and −1 otherwise
-- statement:
--   Total correctness of the `static` function `crypto_onetimeauth_poly1305_donna_verify` in Debian's AArch64 object code of libsodium's `poly1305_donna.c` (in `libsodiumDebianOnetimeauthCtLib`, which also holds the code of `crypto_verify_16` that it calls), under the contract `verifySpec`, for every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`verifyOk`, that is `dataOk`, bundle `Poly1305DebianApi_Spec`). The function is a symbol of the code block, though not exported. For every ghost value $(roH, roM, roK, h, m, key, g)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition and holds the library's data objects in their initial state (`PlacedLib.dataInit`), separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched, the data objects unchanged and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the 16 bytes $h$, `x1` to the message bytes $m$ with `x2` $= |m|$, and `x3` to the 32 key bytes $key$, each owned or read-only as $roH$, $roM$, $roK$ say; the stack-protector guard with value $g$ is readable where the code reads it (`guard pl g`); the caller lends the 4352 bytes below the stack pointer.
--   - **After:** `w0` is `0` if $h$ = `poly1305Mac m key` (RFC 8439 §2.5.1) and `0xffffffff` (the C `int` $-1$) otherwise (`okResult`); $h$, $m$, $key$, the guard and the stack frame are handed back unchanged.
--
--   `poly1305_donna.c`, lines 102–113: “unsigned char correct[16]; crypto_onetimeauth_poly1305_donna(correct, in, inlen, k); return crypto_verify_16(h, correct);”
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 102–116 (crypto_onetimeauth_poly1305_donna_verify)

import Definitions.Def_Poly1305DebianApi_Spec

namespace Poly1305DebianApi

theorem verifyOk_donna_verify :
    verifyOk "crypto_onetimeauth_poly1305_donna_verify [libsodium_la_poly1305_donna]" := by
  sorry

end Poly1305DebianApi
