-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_rk4_order4
-- name    : RungeKuttaOrderConditions.Butcher.rk4_order4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:58:17.918809+00:00
-- url     : https://prove2.me/theorems/94d760b6-b756-4473-b732-3dd856e92e70
-- title:
--   Butcher: rk4 order4
-- statement:
--   classic RK4 satisfies ALL order-≤4 conditions, certified, axiom-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L455-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L455-L457

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

theorem RungeKuttaOrderConditions.Butcher.rk4_order4 : satisfiesOrderConditions rk4A rk4B 4 := by sorry
