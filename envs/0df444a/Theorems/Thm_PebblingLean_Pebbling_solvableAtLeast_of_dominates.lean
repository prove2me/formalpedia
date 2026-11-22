-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_of_dominates
-- name    : PebblingLean.Pebbling.solvableAtLeast_of_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:51.138657+00:00
-- url     : https://prove2.me/theorems/f9f6cb73-cfc0-4f9d-9977-87fe6827f6fb
-- title:
--   Pebbling: solvable At Least of dominates
-- statement:
--   Extra pebbles cannot hurt `T`-solvability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L230-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L230-L234

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

theorem PebblingLean.Pebbling.solvableAtLeast_of_dominates [DecidableEq V] {G : Graph V} {D D' : Pebbling V}
    {T : ℕ} (hsolv : SolvableAtLeast G D T) (hdom : Dominates D' D) :
    SolvableAtLeast G D' T := by sorry
