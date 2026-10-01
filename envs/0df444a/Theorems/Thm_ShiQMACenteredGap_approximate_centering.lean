-- Prove2me | Theorems.Thm_ShiQMACenteredGap_approximate_centering
-- name    : ShiQMACenteredGap.approximate_centering
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T09:11:43.369773+00:00
-- url     : https://prove2.me/theorems/dc338b7f-9946-4b9e-aed0-6f006b829bb4
-- title:
--   Affine coin approximation preserves an acceptance bias
-- statement:
--   If the auxiliary coin probability is within one quarter of the original completeness–soundness gap, affine centering preserves at least one eighth of that gap on each side of one half.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/c9e136b/proofs/AMPUNI-affine-centering.lean#L37-L51

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem ShiQMACenteredGap.approximate_centering {a b u : ℝ}
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    (∀ t : ℝ, a ≤ t → 1 / 2 + (a - b) / 8 ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - (a - b) / 8) := by
  sorry
