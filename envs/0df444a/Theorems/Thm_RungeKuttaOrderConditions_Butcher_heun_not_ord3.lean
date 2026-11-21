-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_heun_not_ord3
-- name    : RungeKuttaOrderConditions.Butcher.heun_not_ord3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:54.540743+00:00
-- url     : https://prove2.me/theorems/b3845039-b62d-435b-aa25-ac82cc711516
-- title:
--   Butcher: heun not ord3
-- statement:
--   The Butcher construction uses the heun not ord3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L319-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L319-L319

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

theorem RungeKuttaOrderConditions.Butcher.heun_not_ord3 : ¬ orderCond heunA heunB t31 := by sorry
