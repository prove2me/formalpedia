-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_strictIntermediate_card_eq_sub_two
-- name    : SharpIntermediateSubgroupBounds.strictIntermediate_card_eq_sub_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:53:19.416104+00:00
-- url     : https://prove2.me/theorems/cc18e49e-40b8-4c92-ace5-6ea033458da7
-- title:
--   Sharp Intermediate Subgroup Bounds: strict Intermediate card eq sub two
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the strict Intermediate card eq sub two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L707-L710
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L707-L710

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

theorem SharpIntermediateSubgroupBounds.strictIntermediate_card_eq_sub_two (H : Subgroup G) (hHt : H < ⊤) :
    Nat.card (strictIntermediate H) = Nat.card (interval H) - 2 := by sorry
