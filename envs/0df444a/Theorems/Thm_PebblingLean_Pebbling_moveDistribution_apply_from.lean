-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
-- name    : PebblingLean.Pebbling.moveDistribution_apply_from
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:12.214472+00:00
-- url     : https://prove2.me/theorems/82e47383-6525-4db8-a482-19e01bc48020
-- title:
--   Pebbling: move Distribution apply from
-- statement:
--   The Pebbling construction uses the move Distribution apply from property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L82-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L82-L84

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

theorem PebblingLean.Pebbling.moveDistribution_apply_from [DecidableEq V] (D : Pebbling V) {u v : V} :
    moveDistribution D u v u = D u - 2 := by sorry
