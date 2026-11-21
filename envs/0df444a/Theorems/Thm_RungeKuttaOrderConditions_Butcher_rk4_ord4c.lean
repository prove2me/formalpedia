-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_rk4_ord4c
-- name    : RungeKuttaOrderConditions.Butcher.rk4_ord4c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:58:14.5629+00:00
-- url     : https://prove2.me/theorems/a3518a45-ce2c-43f8-9b1b-f842442cfc37
-- title:
--   Butcher: rk4 ord4c
-- statement:
--   The Butcher construction uses the rk4 ord4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L328-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L328-L328

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

theorem RungeKuttaOrderConditions.Butcher.rk4_ord4c : orderCond rk4A rk4B t43 := by sorry
