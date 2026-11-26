-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_quarterShiftScale_mul_centered_power
-- name    : SharpIntermediateSubgroupBounds.quarterShiftScale_mul_centered_power
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:24.529629+00:00
-- url     : https://prove2.me/theorems/38ee448b-0983-452e-83ef-f427beb2b397
-- title:
--   Sharp Intermediate Subgroup Bounds: quarter Shift Scale mul centered power
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the quarter Shift Scale mul centered power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L935-L946
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L935-L946

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.quarterShiftScale_mul_centered_power {p a : ℕ} (hp : 2 ≤ p) :
    quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) =
      Real.rpow (p : ℝ) (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4)) := by sorry
