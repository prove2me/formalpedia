-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_mono
-- name    : PebblingLean.Pebbling.canReachAtLeast_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:22.28634+00:00
-- url     : https://prove2.me/theorems/8649829b-4145-45af-883c-362c47e3a736
-- title:
--   Pebbling: can Reach At Least mono
-- statement:
--   If a distribution can reach a larger demand, it can reach any smaller
--   demand.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L222-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L222-L227

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

theorem PebblingLean.Pebbling.canReachAtLeast_mono [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {target : V} {T T' : ℕ} (hTT' : T' ≤ T)
    (hcan : CanReachAtLeast G D target T) :
    CanReachAtLeast G D target T' := by sorry
