-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_evenUSummand_le
-- name    : SharpIntermediateSubgroupBounds.evenUSummand_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:27.24808+00:00
-- url     : https://prove2.me/theorems/d7fe79f3-11db-527e-8cd3-9fb344c67cdd
-- title:
--   Sharp Intermediate Subgroup Bounds: even USummand le
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the even USummand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1100-L1119
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1100-L1119

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.evenUSummand_le {p a j : ℕ} (hp : 2 ≤ p) :
    evenUSummand p a j ≤
      2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by sorry
