-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_oddGaussianConstant_lt_sharpConstant
-- name    : SharpIntermediateSubgroupBounds.oddGaussianConstant_lt_sharpConstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:15.460883+00:00
-- url     : https://prove2.me/theorems/46784520-a8a0-5757-9f0e-e3226e7bd690
-- title:
--   Sharp Intermediate Subgroup Bounds: odd Gaussian Constant lt sharp Constant
-- statement:
--   The half-integral translate is strictly below the integral theta maximum,
--   so the odd-rank constant is strictly smaller than the even-rank sharp
--   constant under the canonical quarter-square normalization.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L961-L971
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L961-L971

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.oddGaussianConstant_lt_sharpConstant {p : ℝ} (hp : 2 ≤ p) :
    oddGaussianConstant p < sharpConstant p := by sorry
