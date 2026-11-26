-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_le
-- name    : SharpIntermediateSubgroupBounds.normalizedGaussianRight_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:47:39.989827+00:00
-- url     : https://prove2.me/theorems/c873fbf5-e515-4374-b044-f6a5b4712a7b
-- title:
--   Sharp Intermediate Subgroup Bounds: normalized Gaussian Right le
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the normalized Gaussian Right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L356-L390
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L356-L390

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.normalizedGaussianRight_le {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedGaussianRight p a j ≤
      eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by sorry
