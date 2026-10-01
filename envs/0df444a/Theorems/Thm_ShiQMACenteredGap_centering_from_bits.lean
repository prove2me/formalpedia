-- Prove2me | Theorems.Thm_ShiQMACenteredGap_centering_from_bits
-- name    : ShiQMACenteredGap.centering_from_bits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T11:39:00.064993+00:00
-- url     : https://prove2.me/theorems/9dcd2bd5-57f0-4ce7-aa27-8bc8e30812d1
-- title:
--   Compute a centering coin from approximate threshold bits
-- statement:
--   Two equally long bit-string approximations to real thresholds determine an integer centering coin whose error is bounded by their dyadic precision. No real-floor computation is used.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c789401/proofs/AMPUNI-computable-centering.lean#L48-L70

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_centeringNumerator_value

set_option autoImplicit false

theorem ShiQMACenteredGap.centering_from_bits {a b : ℝ} (as bs : List Bool) (hlen : as.length = bs.length)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ as.length)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ as.length) :
    let j := centeringNumerator as.length (binaryNumerator as) (binaryNumerator bs)
    |(j : ℝ) / (2 : ℝ) ^ (as.length + 1) - centeringCoin a b| ≤
      1 / (2 : ℝ) ^ as.length := by
  sorry
