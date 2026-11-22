-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_dominates
-- name    : PebblingLean.Pebbling.canReachAtLeast_of_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:20.147793+00:00
-- url     : https://prove2.me/theorems/5ec0296e-ca61-4de6-b24e-98d25ce18b2a
-- title:
--   Pebbling: can Reach At Least of dominates
-- statement:
--   Extra pebbles cannot hurt target reachability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L213-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L213-L218

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

theorem PebblingLean.Pebbling.canReachAtLeast_of_dominates [DecidableEq V] {G : Graph V} {D D' : Pebbling V}
    {target : V} {T : ℕ} (hcan : CanReachAtLeast G D target T) (hdom : Dominates D' D) :
    CanReachAtLeast G D' target T := by sorry
