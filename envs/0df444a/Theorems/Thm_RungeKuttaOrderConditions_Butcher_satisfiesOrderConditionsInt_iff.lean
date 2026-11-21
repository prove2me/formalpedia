-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_satisfiesOrderConditionsInt_iff
-- name    : RungeKuttaOrderConditions.Butcher.satisfiesOrderConditionsInt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:41.478183+00:00
-- url     : https://prove2.me/theorems/9c1a744d-e4e2-4480-8e52-2886a8dba65e
-- title:
--   Butcher: satisfies Order Conditions Int iff
-- statement:
--   same keystone as `satisfiesOrderConditions_iff`, for the integer condition: the
--       order-p conditions
--       reduce to the finite catalogue check (reuses the generic `build`/`catalog` completeness).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L819-L825
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L819-L825

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

theorem RungeKuttaOrderConditions.Butcher.satisfiesOrderConditionsInt_iff (A : List (List Z15)) (b : List Z15) (D : Int) (p : Nat) :
    satisfiesOrderConditionsInt A b D p ↔ ∀ t ∈ catalog p, orderCondInt A b D t := by sorry
