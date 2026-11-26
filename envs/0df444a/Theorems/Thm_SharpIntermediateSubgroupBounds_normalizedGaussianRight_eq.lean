-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_eq
-- name    : SharpIntermediateSubgroupBounds.normalizedGaussianRight_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:41:30.329087+00:00
-- url     : https://prove2.me/theorems/48ba4204-1c09-5d57-9a59-41bda906d138
-- title:
--   Sharp Intermediate Subgroup Bounds: normalized Gaussian Right eq
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the normalized Gaussian Right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L295-L323
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L295-L323

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.normalizedGaussianRight_eq {p a j : ℕ} (hp : 2 ≤ p) (hj : j ≤ a) :
    normalizedGaussianRight p a j =
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ * (gammaR (p : ℝ) (a - j))⁻¹ := by sorry
