-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerLayer_card_le
-- name    : SharpIntermediateSubgroupBounds.primePowerLayer_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:43:38.675868+00:00
-- url     : https://prove2.me/theorems/44eb857b-b149-549e-9b69-f35b4423484c
-- title:
--   Sharp Intermediate Subgroup Bounds: prime Power Layer card le
-- statement:
--   The Gaussian layer bound for an arbitrary finite group inclusion of prime-power index.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L535-L559
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L535-L559

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

theorem SharpIntermediateSubgroupBounds.primePowerLayer_card_le {p a k : ℕ} (hp : p.Prime) (H : Subgroup G)
    (hindex : H.index = p ^ a) :
    (primePowerLayer p k H ⊤).card ≤ qBinom p a k := by sorry
