-- Prove2me | Theorems.Thm_Poly1305Boringssl_poly1305Mac_eq_poly1305
-- name    : Poly1305Boringssl.poly1305Mac_eq_poly1305
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-24T10:08:29.836994+00:00
-- url     : https://prove2.me/theorems/0800eb07-48da-4a4b-966d-b8e7d8f98495
-- title:
--   RFC 8439, §2.5 — poly1305_mac is Bernstein's Poly1305 with the key split into a clamped r and s
-- statement:
--   For every 32-byte key and every message (lists of bytes), there are 16-byte strings $r$ and $s$ in the sense of Bernstein's paper (bundle `Poly1305Bernstein`) such that
--   - $r$ meets Bernstein's conditions (`Poly1305.IsClamped`): $r[3], r[7], r[11], r[15] < 16$ and $r[4], r[8], r[12]$ divisible by 4;
--   - the little-endian value of $r$ (`Poly1305.leVal`) is the RFC's clamped $r$: `clamp` of the value of the first 16 key bytes;
--   - the value of $s$ is the value of the last 16 key bytes;
--   - `poly1305Mac msg key`, read byte by byte as numbers, is Bernstein's $\mathrm{Poly1305}_r(m, s)$ (`Poly1305.poly1305`), with $r$ given as its value and the message's bytes as Bernstein's bytes.
--
--   RFC 8439, §2.5, p. 14: “Poly1305 is a one-time authenticator designed by D. J. Bernstein. Poly1305 takes a 32-byte one-time key and a message and produces a 16-byte tag.” “Regardless of how the key is generated, the key is partitioned into two parts, called "r" and "s".” “r[3], r[7], r[11], and r[15] are required to have their top four bits clear (be smaller than 16)” and “r[4], r[8], and r[12] are required to have their bottom two bits clear (be divisible by 4)”.
-- source:
--   Y. Nir and A. Langley, ChaCha20 and Poly1305 for IETF Protocols, RFC 8439, June 2018 (https://doi.org/10.17487/RFC8439), §2.5 (pp. 14–16)

import Definitions.Def_Poly1305Boringssl_Rfc8439
import Definitions.Def_Poly1305Bernstein

namespace Poly1305Boringssl

theorem poly1305Mac_eq_poly1305 (key msg : List (BitVec 8)) (hkey : key.length = 32) :
    ∃ r s : Poly1305.Str16, Poly1305.IsClamped r ∧
      Poly1305.leVal r = clamp (leBytesToNum (key.take 16)) ∧
      Poly1305.leVal s = leBytesToNum (key.drop 16) ∧
      (poly1305Mac msg key).map BitVec.toNat =
        List.ofFn fun j =>
          ((Poly1305.poly1305 (Poly1305.leVal r) (msg.map fun b => (⟨b.toNat, b.isLt⟩ : Poly1305.Byte)) s j :
            Poly1305.Byte) : Nat) := by
  sorry

end Poly1305Boringssl
