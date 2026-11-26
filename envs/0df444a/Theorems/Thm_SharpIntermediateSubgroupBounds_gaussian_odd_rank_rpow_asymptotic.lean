-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_odd_rank_rpow_asymptotic
-- name    : SharpIntermediateSubgroupBounds.gaussian_odd_rank_rpow_asymptotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:10.12818+00:00
-- url     : https://prove2.me/theorems/6a72ac15-e396-53e2-b067-a1ff798883dd
-- title:
--   Sharp Intermediate Subgroup Bounds: gaussian odd rank rpow asymptotic
-- statement:
--   Equivalent quarter-square form of the odd-rank asymptotic.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L949-L956
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L949-L956

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.gaussian_odd_rank_rpow_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      Real.rpow (p : ℝ) (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4)) *
        (totalQBinom p (2 * a + 1) : ℝ)) atTop
      (nhds (oddGaussianConstant (p : ℝ))) := by sorry
