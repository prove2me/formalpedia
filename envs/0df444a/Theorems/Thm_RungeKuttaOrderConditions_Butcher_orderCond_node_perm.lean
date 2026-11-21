-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_orderCond_node_perm
-- name    : RungeKuttaOrderConditions.Butcher.orderCond_node_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:58:28.641589+00:00
-- url     : https://prove2.me/theorems/5f67df4d-1241-44dc-b664-e937be439552
-- title:
--   Butcher: order Cond node perm
-- statement:
--   BRIDGE: the order condition depends only on the ABSTRACT tree — permuting children is
--       invisible.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L524-L526
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L524-L526

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

theorem RungeKuttaOrderConditions.Butcher.orderCond_node_perm (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    orderCond A b (.node F) ↔ orderCond A b (.node G) := by sorry
