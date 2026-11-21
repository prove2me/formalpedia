-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_satisfiesOrderConditions_iff
-- name    : RungeKuttaOrderConditions.Butcher.satisfiesOrderConditions_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:42.698301+00:00
-- url     : https://prove2.me/theorems/0fc7faae-e523-4871-98fe-8c8af5db35a4
-- title:
--   Butcher: satisfies Order Conditions iff
-- statement:
--   KEYSTONE: the order-p conditions are equivalent to a finite check over the catalogue.
--       (sound + complete)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L446-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L446-L452

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder
set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]

theorem RungeKuttaOrderConditions.Butcher.satisfiesOrderConditions_iff (A : List (List K)) (b : List K) (p : Nat) :
    satisfiesOrderConditions A b p ↔ ∀ t ∈ catalog p, orderCond A b t := by sorry
