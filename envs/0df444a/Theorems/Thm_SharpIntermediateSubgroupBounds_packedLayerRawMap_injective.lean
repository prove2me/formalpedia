-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_packedLayerRawMap_injective
-- name    : SharpIntermediateSubgroupBounds.packedLayerRawMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:45:38.866873+00:00
-- url     : https://prove2.me/theorems/c3af9f53-9164-47cc-9f98-5a80f3adf90d
-- title:
--   Sharp Intermediate Subgroup Bounds: packed Layer Raw Map injective
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the packed Layer Raw Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L361-L371
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L361-L371

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite

theorem SharpIntermediateSubgroupBounds.packedLayerRawMap_injective (H : Subgroup G) (m r : ℕ) :
    Function.Injective (packedLayerRawMap H m r) := by sorry
