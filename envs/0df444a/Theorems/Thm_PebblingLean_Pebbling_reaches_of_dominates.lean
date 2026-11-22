-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_reaches_of_dominates
-- name    : PebblingLean.Pebbling.reaches_of_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:41.205917+00:00
-- url     : https://prove2.me/theorems/491b5cc8-6226-40b3-8a6c-44f4d2c6748a
-- title:
--   Pebbling: reaches of dominates
-- statement:
--   Any sequence of moves can be replayed from a dominating distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L198-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L198-L210

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

theorem PebblingLean.Pebbling.reaches_of_dominates [DecidableEq V] {G : Graph V} {D E D' : Pebbling V}
    (hreach : Reaches G D E) (hdom : Dominates D' D) :
    ∃ E' : Pebbling V, Reaches G D' E' ∧ Dominates E' E := by sorry
