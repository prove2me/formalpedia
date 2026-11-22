-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_walk_of_single_dominated
-- name    : PebblingLean.Pebbling.canReachAtLeast_of_walk_of_single_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:08.332001+00:00
-- url     : https://prove2.me/theorems/ac4ac6d0-99c7-440b-b28f-384cfb3e4435
-- title:
--   Pebbling: can Reach At Least of walk of single dominated
-- statement:
--   Direct delivery is monotone in the initial distribution: extra pebbles
--   away from the chosen starting pile cannot hurt.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L227-L231
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L227-L231

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.canReachAtLeast_of_walk_of_single_dominated [DecidableEq V] {G : Graph V}
    {D : Pebbling V} {u target : V} (walk : G.Walk u target) {T : ℕ}
    (hdom : Dominates D (single u (T * 2 ^ walk.length))) :
    CanReachAtLeast G D target T := by sorry
