-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_odd_rank_asymptotic
-- name    : SharpIntermediateSubgroupBounds.gaussian_odd_rank_asymptotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:15.008897+00:00
-- url     : https://prove2.me/theorems/add675f8-88cc-4616-a72c-0afc920a47dc
-- title:
--   Sharp Intermediate Subgroup Bounds: gaussian odd rank asymptotic
-- statement:
--   Full half-shifted-theta asymptotic in odd rank.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L914-L933
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L914-L933

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.gaussian_odd_rank_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
        (totalQBinom p (2 * a + 1) : ℝ)) atTop
      (nhds (oddGaussianConstant (p : ℝ))) := by sorry
