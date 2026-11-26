-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_rawRelGen_card_eq_cardH_pow_mul_cosetRelGen_card
-- name    : SharpIntermediateSubgroupBounds.rawRelGen_card_eq_cardH_pow_mul_cosetRelGen_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:44:38.775282+00:00
-- url     : https://prove2.me/theorems/f51e630d-1bc8-4ce9-895e-fb4ffa6d1449
-- title:
--   Sharp Intermediate Subgroup Bounds: raw Rel Gen card eq card H pow mul coset Rel Gen card
-- statement:
--   Symmetric form of the exact representative multiplicity.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L221-L226
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L221-L226

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

theorem SharpIntermediateSubgroupBounds.rawRelGen_card_eq_cardH_pow_mul_cosetRelGen_card
    {H K : Subgroup G} (hHK : H ≤ K) (r : ℕ) :
    Nat.card (RawRelGen H K r) =
      Nat.card H ^ r * Nat.card (CosetRelGen H K r) := by sorry
