-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_move_of_dominates
-- name    : PebblingLean.Pebbling.move_of_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:40.165033+00:00
-- url     : https://prove2.me/theorems/10345c2f-38d0-430f-ad48-0f97928fe046
-- title:
--   Pebbling: move of dominates
-- statement:
--   A single move can be replayed from a dominating distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L186-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L186-L195

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

theorem PebblingLean.Pebbling.move_of_dominates [DecidableEq V] {G : Graph V} {D E D' : Pebbling V}
    (hmove : Move G D E) (hdom : Dominates D' D) :
    ∃ E' : Pebbling V, Move G D' E' ∧ Dominates E' E := by sorry
