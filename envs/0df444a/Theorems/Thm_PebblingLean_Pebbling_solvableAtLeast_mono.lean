-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_mono
-- name    : PebblingLean.Pebbling.solvableAtLeast_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:18.659854+00:00
-- url     : https://prove2.me/theorems/191bce0f-3c72-4517-b75d-22e906aa5e1e
-- title:
--   Pebbling: solvable At Least mono
-- statement:
--   `T`-solvability implies any smaller demand.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L237-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L237-L241

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

theorem PebblingLean.Pebbling.solvableAtLeast_mono [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {T T' : ℕ} (hTT' : T' ≤ T) (hsolv : SolvableAtLeast G D T) :
    SolvableAtLeast G D T' := by sorry
