-- Prove2me | Theorems.Thm_Poly1305DebianApi_internalOk_poly1305_update
-- name    : Poly1305DebianApi.internalOk_poly1305_update
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T11:24:24.569873+00:00
-- url     : https://prove2.me/theorems/37135409-2a72-5349-9caa-d23d0a32ebd0
-- title:
--   poly1305_donna.c, poly1305_update — buffers a partial block and runs the block loop on the complete ones
-- statement:
--   Total correctness of the internal function `poly1305_update` in Debian's AArch64 object code of libsodium's `poly1305_donna.c` (in `libsodiumDebianOnetimeauthCtLib`), under the contract `updateIntSpec`, for every placement of the library the linker could produce that treats every GOT access to `__stack_chk_guard` alike (`GuardUniform`), and every hook table laid out as a real link lays it out (`Link.PlacedLib.LinkOk`) whose hooks for `sodium_memzero` and `memset` meet `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec` (`internalOk`, bundle `Poly1305DebianApi_Spec`); the function calls no hook. The function is a symbol of the code block, though not exported. For every ghost value $(ro, st, m)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the 96 owned state bytes $st$, whose first 48 (`r` and `h`) satisfy `StateOk` and whose `leftover` (offset 64) is below 16; the bytes $m$ are at `x1`, owned or read-only as $ro$ says; `x2` $= |m|$; the caller lends the 32 bytes below the stack pointer.
--   - **After:** `x0` is unchanged, and it points to 96 bytes $st'$ with `Absorbs st m st'`. Let $L$ be `leftover`, $t$ the first $L$ bytes of `buffer` (offset 72) followed by $m$, and $k$ the largest multiple of 16 that is at most $|t|$. Then $st'$ keeps $r$, `pad` and `final`, satisfies `StateOk` on its first 48 bytes, has `leftover` $= |t| - k$ with the last $|t| - k$ bytes of $t$ at the start of `buffer`, and has an accumulator congruent modulo $2^{130} - 5$ to $h \leftarrow r \cdot (h + n + b) \bmod (2^{130} - 5)$ run over the $k/16$ complete blocks of $t$, from the old accumulator (`blocksAcc`, with $b = 2^{128}$ if `final` is 0, else 0). $m$ and the stack frame are handed back.
--
--   `poly1305_donna.c`, lines 20, 40 and 49: “/* handle leftover */”, “/* process full blocks */”, “/* store leftover */”.
--
--   **Replaces** [`Poly1305Debian.internalOk_poly1305_update`](https://prove2.me/theorems/0e2f3c7d-339b-5e86-9db0-736fe98e56b1), the same contract for the library `libsodiumDebianOnetimeauthLib` of the first three objects alone; `libsodiumDebianOnetimeauthCtLib` adds `verify.o` after them, so that all of libsodium's Poly1305 API, verification included, is stated over one library.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 14–56 (poly1305_update)

import Definitions.Def_Poly1305DebianApi_Spec

namespace Poly1305DebianApi

theorem internalOk_poly1305_update :
    internalOk "poly1305_update [libsodium_la_poly1305_donna]" (fun _ => updateIntSpec) := by
  sorry

end Poly1305DebianApi
