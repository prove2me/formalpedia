-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_solvable_of_solvableAtLeast
-- name    : PebblingLean.Pebbling.solvable_of_solvableAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:19.850346+00:00
-- url     : https://prove2.me/theorems/9322db3c-0b95-41ca-a2de-a366c256d521
-- title:
--   Pebbling: solvable of solvable At Least
-- statement:
--   A distribution that is `T`-solvable for `T ≥ 1` is solvable in the usual
--   one-pebble sense.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L245-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L245-L248

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

theorem PebblingLean.Pebbling.solvable_of_solvableAtLeast [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {T : ℕ} (hT : 1 ≤ T) (hsolv : SolvableAtLeast G D T) :
    Solvable G D := by sorry
