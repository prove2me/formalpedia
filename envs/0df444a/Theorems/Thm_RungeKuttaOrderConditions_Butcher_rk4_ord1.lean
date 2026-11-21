-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_rk4_ord1
-- name    : RungeKuttaOrderConditions.Butcher.rk4_ord1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:55.567186+00:00
-- url     : https://prove2.me/theorems/90e39072-4588-4871-afab-fcf7f889d3db
-- title:
--   Butcher: rk4 ord1
-- statement:
--   The Butcher construction uses the rk4 ord1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L322-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L322-L322

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

theorem RungeKuttaOrderConditions.Butcher.rk4_ord1 : orderCond rk4A rk4B t1  := by sorry
