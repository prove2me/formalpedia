-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_intermediateSubgroups_card_le_totalQBinom
-- name    : SharpIntermediateSubgroupBounds.intermediateSubgroups_card_le_totalQBinom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:54.193386+00:00
-- url     : https://prove2.me/theorems/6af5bd82-ae70-45fe-b2e0-c7a46fc8c975
-- title:
--   Sharp Intermediate Subgroup Bounds: intermediate Subgroups card le total QBinom
-- statement:
--   Exact prime-power interval upper bound.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L584-L607
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L584-L607

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype

theorem SharpIntermediateSubgroupBounds.intermediateSubgroups_card_le_totalQBinom {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    (intermediateSubgroups H).card ≤ totalQBinom p a := by sorry
