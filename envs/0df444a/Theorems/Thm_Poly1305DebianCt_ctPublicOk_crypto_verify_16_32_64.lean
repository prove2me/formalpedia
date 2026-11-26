-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctPublicOk_crypto_verify_16_32_64
-- name    : Poly1305DebianCt.ctPublicOk_crypto_verify_16_32_64
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:19:38.624019+00:00
-- url     : https://prove2.me/theorems/6722eb4c-01a2-5a40-b030-0b3424b8ddc8
-- title:
--   internals/README.md, crypto_verify_16/32/64 — compare secrets in constant time (Debian's libsodium, AArch64)
-- statement:
--   The exports `crypto_verify_16`, `crypto_verify_32` and `crypto_verify_64` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, `verify.o` among them, unmodified) are each constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctPublicOk "crypto_verify_n" (verifyNPre n) verifyNPub` for $n = 16, 32, 64$ (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`). The statement is the conjunction of the three.
--
--   In detail, for each $n$: take two entry states at `crypto_verify_n`'s address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `x` and `y` in `x0` and `x1`. Suppose the memory of each holds, separately from an arbitrary frame of its own, the library's data objects in their initial state and `verifyNPre n` for its own ghost value $(roX, roY, a, b)$: $n$ bytes $a$ at `x` and $n$ bytes $b$ at `y` (each owned or read-only, by $roX$, $roY$), and the 32 bytes below the stack pointer. Suppose the two ghost values agree on $roX$ and $roY$. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever the $2n$ compared bytes are: equal inputs and inputs differing in any byte cannot be told apart this way. Nothing is said about the value returned.
-- source:
--   libsodium documentation, Internals (https://doc.libsodium.org/internals; source jedisct1/libsodium-doc, commit 5adaf345, https://github.com/jedisct1/libsodium-doc/blob/5adaf34515b79d0b37bd8edbe042f20f3bdba2c6/internals/README.md), line 50 ("Secrets are always compared in constant time using sodium_memcmp() or crypto_verify_(16|32|64)()"), implemented by src/libsodium/crypto_verify/verify.c lines 60–103 (crypto_verify_n, crypto_verify_16, _32, _64) of libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctPublicOk_crypto_verify_16_32_64 :
    ctPublicOk "crypto_verify_16" (verifyNPre 16) verifyNPub ∧
      ctPublicOk "crypto_verify_32" (verifyNPre 32) verifyNPub ∧
        ctPublicOk "crypto_verify_64" (verifyNPre 64) verifyNPub := by
  sorry

end Poly1305DebianCt
