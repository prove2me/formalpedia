-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedOddGaussianRight_eq
-- name    : SharpIntermediateSubgroupBounds.normalizedOddGaussianRight_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:43:42.259151+00:00
-- url     : https://prove2.me/theorems/35c3f330-56f2-4315-bdcd-d6f9dfa686a4
-- title:
--   Sharp Intermediate Subgroup Bounds: normalized Odd Gaussian Right eq
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the normalized Odd Gaussian Right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L619-L651
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L619-L651

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.normalizedOddGaussianRight_eq {p a j : ℕ} (hp : 2 ≤ p) (hj : j ≤ a) :
    normalizedOddGaussianRight p a j =
      (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
        (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by sorry
