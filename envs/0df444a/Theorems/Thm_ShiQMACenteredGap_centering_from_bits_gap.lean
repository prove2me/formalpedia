-- Prove2me | Theorems.Thm_ShiQMACenteredGap_centering_from_bits_gap
-- name    : ShiQMACenteredGap.centering_from_bits_gap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T11:54:04.619648+00:00
-- url     : https://prove2.me/theorems/0a1b9a59-3f46-40e8-a8b5-aaca0b90cf02
-- title:
--   Threshold bit approximations meet the QMA centering tolerance
-- statement:
--   At logarithmic precision chosen from an inverse gap budget q, the computed integer coin numerator is in range and its dyadic value lies within one quarter of the completeness–soundness gap of the ideal centering coin.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c789401/proofs/AMPUNI-computable-centering.lean#L72-L93

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_centering_from_bits

set_option autoImplicit false

theorem ShiQMACenteredGap.centering_from_bits_gap {a b : ℝ} (hab : b ≤ a)
    (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (as bs : List Bool) (haLen : as.length = coinBits q) (hbLen : bs.length = coinBits q)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ coinBits q)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ coinBits q) :
    let j := centeringNumerator (coinBits q) (binaryNumerator as) (binaryNumerator bs)
    j ≤ 2 ^ (coinBits q + 1) ∧
      |(j : ℝ) / (2 : ℝ) ^ (coinBits q + 1) - centeringCoin a b| ≤ (a - b) / 4 := by
  sorry
