-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_le_eulerC
-- name    : SharpIntermediateSubgroupBounds.normalizedGaussianRight_le_eulerC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:38.306399+00:00
-- url     : https://prove2.me/theorems/2130d934-e1e2-4f12-af0f-e992314c677b
-- title:
--   Sharp Intermediate Subgroup Bounds: normalized Gaussian Right le euler C
-- statement:
--   The sharp one-sided Gaussian majorant used in the manuscript.  One
--   inverse Euler factor cancels against the longer numerator product, leaving
--   only a single factor `C_p`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L395-L431
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L395-L431

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.normalizedGaussianRight_le_eulerC {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedGaussianRight p a j ≤
      eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by sorry
