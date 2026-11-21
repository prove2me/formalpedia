-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_gauss_order4
-- name    : RungeKuttaOrderConditions.Butcher.gauss_order4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:58:32.097773+00:00
-- url     : https://prove2.me/theorems/1a98670b-d689-47db-af9b-c710ba5f5c8e
-- title:
--   Butcher: gauss order4
-- statement:
--   The Butcher construction uses the gauss order4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L770-L781
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L770-L781

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

theorem RungeKuttaOrderConditions.Butcher.gauss_order4 : satisfiesOrderConditions gaussA gaussB 4 := by sorry
