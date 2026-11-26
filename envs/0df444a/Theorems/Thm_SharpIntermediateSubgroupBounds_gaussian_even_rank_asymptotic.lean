-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_even_rank_asymptotic
-- name    : SharpIntermediateSubgroupBounds.gaussian_even_rank_asymptotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:34.732698+00:00
-- url     : https://prove2.me/theorems/33c87887-d6fc-4043-ae93-ed0e175857c1
-- title:
--   Sharp Intermediate Subgroup Bounds: gaussian even rank asymptotic
-- statement:
--   Full-constant asymptotic for the number of subspaces in even rank.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L562-L597
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L562-L597

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.gaussian_even_rank_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ)) atTop
      (nhds (sharpConstant (p : ℝ))) := by sorry
