-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerLayer_card_subgroup
-- name    : SharpIntermediateSubgroupBounds.primePowerLayer_card_subgroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:49:46.778234+00:00
-- url     : https://prove2.me/theorems/da4fe701-779c-57d4-b6e0-711c1fb4c821
-- title:
--   Sharp Intermediate Subgroup Bounds: prime Power Layer card subgroup
-- statement:
--   Passing from an ambient subgroup `P` to the group `P` itself preserves every relative-index
--   layer.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L172-L212
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L172-L212

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

theorem SharpIntermediateSubgroupBounds.primePowerLayer_card_subgroup {p k : ℕ} {T P : Subgroup G} (hTP : T ≤ P) :
    (primePowerLayer p k T P).card =
      (primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P)).card := by sorry
