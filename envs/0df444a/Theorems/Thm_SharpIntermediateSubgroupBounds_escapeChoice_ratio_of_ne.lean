-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_escapeChoice_ratio_of_ne
-- name    : SharpIntermediateSubgroupBounds.escapeChoice_ratio_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:38.220042+00:00
-- url     : https://prove2.me/theorems/47529232-bb9b-4048-b543-aeaa564954be
-- title:
--   Sharp Intermediate Subgroup Bounds: escape Choice ratio of ne
-- statement:
--   Exact normalized branching degree at a proper state.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L333-L355
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L333-L355

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

theorem SharpIntermediateSubgroupBounds.escapeChoice_ratio_of_ne (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 ≠ K) :
    (Fintype.card (EscapeChoice K s) : ℚ) / Nat.card K =
      1 - 1 / (s.1.relIndex K : ℚ) := by sorry
