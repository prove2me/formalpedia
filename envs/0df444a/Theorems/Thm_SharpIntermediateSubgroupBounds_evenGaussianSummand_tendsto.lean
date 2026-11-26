-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_evenGaussianSummand_tendsto
-- name    : SharpIntermediateSubgroupBounds.evenGaussianSummand_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:53.393695+00:00
-- url     : https://prove2.me/theorems/6621165d-57c9-45cb-ae56-4b0d4de3058a
-- title:
--   Sharp Intermediate Subgroup Bounds: even Gaussian Summand tendsto
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the even Gaussian Summand tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L468-L471
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L468-L471

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.evenGaussianSummand_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ evenGaussianSummand p a j) atTop
      (nhds (evenGaussianLimitSummand p j)) := by sorry
