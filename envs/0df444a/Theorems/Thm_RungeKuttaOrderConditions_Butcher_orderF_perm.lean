-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_orderF_perm
-- name    : RungeKuttaOrderConditions.Butcher.orderF_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:38.618182+00:00
-- url     : https://prove2.me/theorems/73a02b2b-07cb-47b2-bec2-ccc8d8c60f66
-- title:
--   Butcher: order F perm
-- statement:
--   The Butcher construction uses the order F perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L499-L504
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L499-L504

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

theorem RungeKuttaOrderConditions.Butcher.orderF_perm {F G : Forest} (h : F.Perm G) : orderF F = orderF G := by sorry
