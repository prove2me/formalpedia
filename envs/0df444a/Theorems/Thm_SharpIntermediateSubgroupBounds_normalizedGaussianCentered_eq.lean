-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianCentered_eq
-- name    : SharpIntermediateSubgroupBounds.normalizedGaussianCentered_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:54:55.204804+00:00
-- url     : https://prove2.me/theorems/0f2dcdf8-10d6-5624-a725-b25a73ba1137
-- title:
--   Sharp Intermediate Subgroup Bounds: normalized Gaussian Centered eq
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the normalized Gaussian Centered eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L437-L443
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L437-L443

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.normalizedGaussianCentered_eq {p a : ℕ} {j : ℤ} (hp : 2 ≤ p)
    (hj : j.natAbs ≤ a) :
    normalizedGaussianCentered p a j =
      (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j.natAbs))⁻¹ *
          (gammaR (p : ℝ) (a - j.natAbs))⁻¹ := by sorry
