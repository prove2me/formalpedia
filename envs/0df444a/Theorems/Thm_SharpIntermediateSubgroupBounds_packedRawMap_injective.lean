-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_packedRawMap_injective
-- name    : SharpIntermediateSubgroupBounds.packedRawMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:45:23.498128+00:00
-- url     : https://prove2.me/theorems/d6aed0b4-cdde-4077-8e7f-f77688808c4e
-- title:
--   Sharp Intermediate Subgroup Bounds: packed Raw Map injective
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the packed Raw Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L71-L81
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L71-L81

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

theorem SharpIntermediateSubgroupBounds.packedRawMap_injective (H : Subgroup G) (q r : ℕ) :
    Function.Injective (packedRawMap H q r) := by sorry
