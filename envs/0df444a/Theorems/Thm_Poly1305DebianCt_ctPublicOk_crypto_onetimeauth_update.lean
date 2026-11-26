-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctPublicOk_crypto_onetimeauth_update
-- name    : Poly1305DebianCt.ctPublicOk_crypto_onetimeauth_update
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:22:53.442673+00:00
-- url     : https://prove2.me/theorems/74fadf62-4838-4247-86f2-b30ddd2abf1f
-- title:
--   advanced/poly1305.md, crypto_onetimeauth_update — constant time for a given buffered count and length (Debian's libsodium, AArch64)
-- statement:
--   The export `crypto_onetimeauth_update` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctPublicOk "crypto_onetimeauth_update" updatePre updatePub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `state`, `in` and `inlen` in `x0`–`x2`. Suppose the memory of each holds, separately from an arbitrary frame of its own, the library's data objects in their initial state and `updatePre` for its own ghost value $(ro, st, inp)$: 256 owned state bytes $st$ at `state` whose `leftover` word (offset 64) is below 16, the input bytes $inp$ at `in` (owned or read-only, by $ro$) with `inlen` $= |inp|$, and the 48 bytes below the stack pointer. Suppose the two ghost values agree on $ro$ and on the `leftover` word. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever the other state bytes and the input bytes are. No invariant on the state is assumed.
-- source:
--   libsodium documentation, Secret-key single-message authentication using Poly1305 (https://doc.libsodium.org/advanced/poly1305; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/advanced/poly1305.md), lines 84–88 and 98 (crypto_onetimeauth_update), implemented by crypto_onetimeauth.c lines 45–52 and poly1305_donna.c lines 83–91 of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctPublicOk_crypto_onetimeauth_update :
    ctPublicOk "crypto_onetimeauth_update" updatePre updatePub := by
  sorry

end Poly1305DebianCt
