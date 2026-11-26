-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
-- name    : SharpIntermediateSubgroupBounds.rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:40.760058+00:00
-- url     : https://prove2.me/theorems/5a86c894-4c49-5c5d-9509-e7ba5357a534
-- title:
--   Sharp Intermediate Subgroup Bounds: raw Rel Gen card eq coset Rel Gen card mul card H pow
-- statement:
--   Exact representative multiplicity: every generating coset tuple has
--   exactly `|H|^r` raw representative tuples.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L207-L218
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L207-L218

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

theorem SharpIntermediateSubgroupBounds.rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
    {H K : Subgroup G} (hHK : H ≤ K) (r : ℕ) :
    Nat.card (RawRelGen H K r) =
      Nat.card (CosetRelGen H K r) * Nat.card H ^ r := by sorry
