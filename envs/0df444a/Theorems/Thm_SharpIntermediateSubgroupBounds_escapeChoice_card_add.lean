-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_escapeChoice_card_add
-- name    : SharpIntermediateSubgroupBounds.escapeChoice_card_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:49.020712+00:00
-- url     : https://prove2.me/theorems/3e916cfa-b260-4ca0-bf0b-6b09468cf148
-- title:
--   Sharp Intermediate Subgroup Bounds: escape Choice card add
-- statement:
--   At a proper state, the allowed choices and the elements of the state
--   partition the target.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L294-L330
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L294-L330

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq

theorem SharpIntermediateSubgroupBounds.escapeChoice_card_add (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 ≠ K) :
    Fintype.card (EscapeChoice K s) + Nat.card s.1 = Nat.card K := by sorry
