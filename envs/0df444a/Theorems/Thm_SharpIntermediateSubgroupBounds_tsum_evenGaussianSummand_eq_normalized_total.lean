-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_evenGaussianSummand_eq_normalized_total
-- name    : SharpIntermediateSubgroupBounds.tsum_evenGaussianSummand_eq_normalized_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:47:43.853535+00:00
-- url     : https://prove2.me/theorems/0e8ccf23-512f-58fc-9a72-1e8cfd89b91c
-- title:
--   Sharp Intermediate Subgroup Bounds: tsum even Gaussian Summand eq normalized total
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the tsum even Gaussian Summand eq normalized total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L490-L520
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L490-L520

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.tsum_evenGaussianSummand_eq_normalized_total {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenGaussianSummand p a j =
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) := by sorry
