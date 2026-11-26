-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_totalQBinom_odd_split
-- name    : SharpIntermediateSubgroupBounds.totalQBinom_odd_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:59.504226+00:00
-- url     : https://prove2.me/theorems/440e731f-5e36-4a81-bae0-c2d01b5accfb
-- title:
--   Sharp Intermediate Subgroup Bounds: total QBinom odd split
-- statement:
--   Odd rank has no single central layer: the lower and upper halves pair
--   exactly.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L759-L781
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L759-L781

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.totalQBinom_odd_split {q : ℕ} (hq : 2 ≤ q) (a : ℕ) :
    totalQBinom q (2 * a + 1) =
      2 * ∑ j ∈ Finset.range (a + 1), qBinom q (2 * a + 1) (a + 1 + j) := by sorry
