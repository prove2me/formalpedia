-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_pGroup_primePowerLayer_card_le
-- name    : SharpIntermediateSubgroupBounds.pGroup_primePowerLayer_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:49.78165+00:00
-- url     : https://prove2.me/theorems/970f1b12-0ca5-5fc7-90ef-23b7a96ce961
-- title:
--   Sharp Intermediate Subgroup Bounds: p Group prime Power Layer card le
-- statement:
--   The Gaussian layer bound for an arbitrary subgroup of a finite `p`-group.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L215-L378
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L215-L378

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

theorem SharpIntermediateSubgroupBounds.pGroup_primePowerLayer_card_le {p a : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (T : Subgroup G) (hindex : T.index = p ^ a) (k : ℕ) :
    (primePowerLayer p k T ⊤).card ≤ qBinom p a k := by sorry
