-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
-- name    : PebblingLean.Pebbling.moveDistribution_apply_to
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:15.450835+00:00
-- url     : https://prove2.me/theorems/8674c61e-8649-4b2d-82de-eda57ea6fd59
-- title:
--   Pebbling: move Distribution apply to
-- statement:
--   The Pebbling construction uses the move Distribution apply to property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L87-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L87-L89

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

theorem PebblingLean.Pebbling.moveDistribution_apply_to [DecidableEq V] (D : Pebbling V) {u v : V} (h : v ≠ u) :
    moveDistribution D u v v = D v + 1 := by sorry
