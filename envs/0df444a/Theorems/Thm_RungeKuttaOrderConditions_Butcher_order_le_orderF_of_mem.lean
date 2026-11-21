-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_order_le_orderF_of_mem
-- name    : RungeKuttaOrderConditions.Butcher.order_le_orderF_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:58:14.559532+00:00
-- url     : https://prove2.me/theorems/39d4b3e4-8c30-4e12-a429-27ee689d7880
-- title:
--   Butcher: order le order F of mem
-- statement:
--   The Butcher construction uses the order le order F of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L346-L354
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L346-L354

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

theorem RungeKuttaOrderConditions.Butcher.order_le_orderF_of_mem : ∀ {c : RTree} {F : Forest}, c ∈ F → order c ≤ orderF F := by sorry
