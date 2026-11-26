-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_half_eq_quarterShiftScale_mul_tsum
-- name    : SharpIntermediateSubgroupBounds.shiftedTheta_half_eq_quarterShiftScale_mul_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:13.016296+00:00
-- url     : https://prove2.me/theorems/8f17522f-736d-4bc8-9ecd-15c7a47e4eab
-- title:
--   Sharp Intermediate Subgroup Bounds: shifted Theta half eq quarter Shift Scale mul tsum
-- statement:
--   The half-shifted theta series is exactly the paired odd Gaussian series,
--   including the quarter-power normalization.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L823-L872
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L823-L872

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.shiftedTheta_half_eq_quarterShiftScale_mul_tsum {p : ℕ} (hp : 2 ≤ p) :
    shiftedTheta (p : ℝ) (1 / 2) = quarterShiftScale (p : ℝ) *
      (2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1))) := by sorry
