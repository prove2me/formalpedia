-- Prove2me | Theorems.Thm_Poly1305DebianApi_dataOk_crypto_verify_16_32_64
-- name    : Poly1305DebianApi.dataOk_crypto_verify_16_32_64
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T11:24:22.498076+00:00
-- url     : https://prove2.me/theorems/10da6e5f-2c82-57b6-95eb-fcb2571a62a9
-- title:
--   verify.c, crypto_verify_16, _32 and _64 — return 0 if the two inputs are equal and −1 otherwise
-- statement:
--   Total correctness of `crypto_verify_16`, `crypto_verify_32` and `crypto_verify_64` in Debian's AArch64 object code of libsodium's `crypto_verify/verify.c` (in `libsodiumDebianOnetimeauthCtLib`), each under the contract `verifyNSpec n` for its $n$ = 16, 32, 64, for every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`dataOk`, bundle `Poly1305DebianApi_Spec`); the functions call no hook. Each function is a symbol of the code block. For every ghost value $(roX, roY, a, b)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition and holds the library's data objects in their initial state (`PlacedLib.dataInit`), separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched, the data objects unchanged and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the $n$ bytes $a$ and `x1` to the $n$ bytes $b$, each owned or read-only as $roX$, $roY$ say; the caller lends the 32 bytes below the stack pointer.
--   - **After:** `w0` is `0` if $a = b$ and `0xffffffff` (the C `int` $-1$) otherwise (`okResult`); $a$, $b$ and the stack frame are handed back unchanged.
--
--   `verify.c`, lines 62–83 and 87–103: `crypto_verify_n` ORs the bytewise differences of its two inputs into a `volatile` accumulator, “for (i = 0; i < n; i++) { d |= x[i] ^ y[i]; }”, then computes “d--; d = ((d >> 13) ^ optblocker_u16) >> 2; return (int) d - 1;”; `crypto_verify_16`, `crypto_verify_32` and `crypto_verify_64` return `crypto_verify_n` with $n$ = 16, 32 and 64.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_verify/verify.c lines 60–103 (crypto_verify_n, crypto_verify_16, _32, _64)

import Definitions.Def_Poly1305DebianApi_Spec

namespace Poly1305DebianApi

theorem dataOk_crypto_verify_16_32_64 :
    dataOk "crypto_verify_16" (fun _ => verifyNSpec 16) ∧
      dataOk "crypto_verify_32" (fun _ => verifyNSpec 32) ∧
      dataOk "crypto_verify_64" (fun _ => verifyNSpec 64) := by
  sorry

end Poly1305DebianApi
