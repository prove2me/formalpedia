-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
-- name    : PebblingLean.Pebbling.moveDistribution_apply_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:14.211555+00:00
-- url     : https://prove2.me/theorems/1bdcad5c-6659-4ad5-917c-2c703750594b
-- title:
--   Pebbling: move Distribution apply of ne
-- statement:
--   The Pebbling construction uses the move Distribution apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L92-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L92-L95

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.moveDistribution_apply_of_ne [DecidableEq V] (D : Pebbling V) {u v x : V}
    (hxu : x ≠ u) (hxv : x ≠ v) :
    moveDistribution D u v x = D x := by sorry
