-- Prove2me | Theorems.Thm_ShiQMACenteredGap_centeringNumerator_value
-- name    : ShiQMACenteredGap.centeringNumerator_value
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T11:25:08.240611+00:00
-- url     : https://prove2.me/theorems/baf88213-24a0-4750-81c1-0979af253e3d
-- title:
--   Integer centering numerator represents the affine coin
-- statement:
--   If two natural numerators A and B fit in k fractional bits, the integer centering numerator represents one minus the average of their dyadic values.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c789401/proofs/AMPUNI-computable-centering.lean#L38-L46

import Definitions.Def_ShiQMACenteredGapComputableCoin

set_option autoImplicit false

theorem ShiQMACenteredGap.centeringNumerator_value (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    (centeringNumerator k A B : ℝ) / (2 : ℝ) ^ (k + 1) =
      1 - ((A : ℝ) / (2 : ℝ) ^ k + (B : ℝ) / (2 : ℝ) ^ k) / 2 := by
  sorry
