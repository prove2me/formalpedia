-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_oddGaussianSummand_eq_normalized_total
-- name    : SharpIntermediateSubgroupBounds.tsum_oddGaussianSummand_eq_normalized_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:07.551975+00:00
-- url     : https://prove2.me/theorems/51d05be3-05e1-43a0-92b8-60420104a1bb
-- title:
--   Sharp Intermediate Subgroup Bounds: tsum odd Gaussian Summand eq normalized total
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the tsum odd Gaussian Summand eq normalized total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L783-L812
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L783-L812

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.tsum_oddGaussianSummand_eq_normalized_total {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, oddGaussianSummand p a j =
      quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
        (totalQBinom p (2 * a + 1) : ℝ) := by sorry
