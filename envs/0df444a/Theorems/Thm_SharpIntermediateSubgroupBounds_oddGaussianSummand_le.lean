-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_oddGaussianSummand_le
-- name    : SharpIntermediateSubgroupBounds.oddGaussianSummand_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:13.556982+00:00
-- url     : https://prove2.me/theorems/6471e068-9325-5949-b649-b5e8e157abbf
-- title:
--   Sharp Intermediate Subgroup Bounds: odd Gaussian Summand le
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the odd Gaussian Summand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L898-L911
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L898-L911

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.oddGaussianSummand_le {p a j : ℕ} (hp : 2 ≤ p) :
    oddGaussianSummand p a j ≤
      2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
        (p : ℝ)⁻¹ ^ (j * (j + 1)) := by sorry
