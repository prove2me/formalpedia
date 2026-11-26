-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctPublicOk_crypto_onetimeauth
-- name    : Poly1305DebianCt.ctPublicOk_crypto_onetimeauth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T10:21:47.7854+00:00
-- url     : https://prove2.me/theorems/7ede201c-ff1c-5201-8ee0-66f99f2069d1
-- title:
--   advanced/poly1305.md, crypto_onetimeauth — constant time in the key and the message (Debian's libsodium, AArch64)
-- statement:
--   The export `crypto_onetimeauth` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctPublicOk "crypto_onetimeauth" oneshotPre oneshotPub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `out`, `in`, `inlen` and `k` in `x0`–`x3`. Suppose the memory of each holds, separately from an arbitrary frame of its own, the library's data objects in their initial state and `oneshotPre` for its own ghost value $(roM, roK, ga, out, m, key, g)$: 16 owned bytes at `out`, the message bytes $m$ at `in` with `inlen` $= |m|$ and 32 bytes $key$ at `k` (each owned or read-only, by $roM$, $roK$), the stack-protector guard with value $g$ where the code reads it (through a GOT slot holding the address $ga$ unless the linker relaxed the accesses), and the 4320 bytes below the stack pointer. Suppose the two ghost values agree on $roM$, $roK$ and $ga$. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever the message, key, output and guard bytes are.
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 61–66 (crypto_onetimeauth), implemented by crypto_onetimeauth.c lines 23–28 and poly1305_donna.c lines 58–70 of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctPublicOk_crypto_onetimeauth :
    ctPublicOk "crypto_onetimeauth" oneshotPre oneshotPub := by
  sorry

end Poly1305DebianCt
