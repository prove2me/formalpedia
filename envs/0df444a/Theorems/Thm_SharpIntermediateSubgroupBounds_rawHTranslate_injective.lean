-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_rawHTranslate_injective
-- name    : SharpIntermediateSubgroupBounds.rawHTranslate_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:45:47.370938+00:00
-- url     : https://prove2.me/theorems/c0a6ca79-4563-414b-9cf9-d2e4fbe66b6d
-- title:
--   Sharp Intermediate Subgroup Bounds: raw HTranslate injective
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the raw HTranslate injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L506-L513
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L506-L513

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

theorem SharpIntermediateSubgroupBounds.rawHTranslate_injective {H K : Subgroup G} {r : ℕ}
    (hHK : H ≤ K) (x : RawRelGen H K r) :
    Function.Injective (rawHTranslate hHK x) := by sorry
