-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_oddGaussianSummand_tendsto
-- name    : SharpIntermediateSubgroupBounds.oddGaussianSummand_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:05.127572+00:00
-- url     : https://prove2.me/theorems/f4ebb3e6-3faa-4624-956a-66e16e041125
-- title:
--   Sharp Intermediate Subgroup Bounds: odd Gaussian Summand tendsto
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the odd Gaussian Summand tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L738-L741
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L738-L741

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.oddGaussianSummand_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ oddGaussianSummand p a j) atTop
      (nhds (oddGaussianLimitSummand p j)) := by sorry
