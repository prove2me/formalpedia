-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerU_even_rank_asymptotic
-- name    : SharpIntermediateSubgroupBounds.primePowerU_even_rank_asymptotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:40.934458+00:00
-- url     : https://prove2.me/theorems/4aa1e6b1-0c0d-4a35-a4e9-5c83acd62260
-- title:
--   Sharp Intermediate Subgroup Bounds: prime Power U even rank asymptotic
-- statement:
--   The finite envelope has the same sharp even-rank asymptotic.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1122-L1142
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1122-L1142

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.primePowerU_even_rank_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a)) atTop
      (nhds (sharpConstant (p : ℝ))) := by sorry
