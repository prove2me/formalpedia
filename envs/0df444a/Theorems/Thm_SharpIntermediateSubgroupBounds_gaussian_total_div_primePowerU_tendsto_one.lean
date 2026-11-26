-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_total_div_primePowerU_tendsto_one
-- name    : SharpIntermediateSubgroupBounds.gaussian_total_div_primePowerU_tendsto_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:39.124235+00:00
-- url     : https://prove2.me/theorems/c12423ba-9170-4765-98c2-57250992f1d8
-- title:
--   Sharp Intermediate Subgroup Bounds: gaussian total div prime Power U tendsto one
-- statement:
--   The elementary-abelian count asymptotically exhausts the finite envelope.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1145-L1159
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1145-L1159

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.gaussian_total_div_primePowerU_tendsto_one {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (totalQBinom p (2 * a) : ℝ) / primePowerU p (2 * a)) atTop (nhds 1) := by sorry
