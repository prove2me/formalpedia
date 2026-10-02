-- Prove2me | Theorems.Thm_ShiQMACenteredGap_fractionBits_numerator
-- name    : ShiQMACenteredGap.fractionBits_numerator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T12:09:51.243743+00:00
-- url     : https://prove2.me/theorems/50eb580f-1a94-4db7-a25d-175aa3fd7e8d
-- title:
--   Fixed-width binary encoder recovers its numerator
-- statement:
--   For every j smaller than 2^k, decoding the k-bit fractional encoding of j returns exactly j.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c789401/proofs/AMPUNI-computable-centering.lean#L105-L123

import Definitions.Def_ShiQMACenteredGapComputableCoin

set_option autoImplicit false

theorem ShiQMACenteredGap.fractionBits_numerator (k j : Nat) (hj : j < 2 ^ k) :
    binaryNumerator (fractionBits k j) = j := by
  sorry
