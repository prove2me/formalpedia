-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_pmul_comm
-- name    : RungeKuttaOrderConditions.Butcher.pmul_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:37.624175+00:00
-- url     : https://prove2.me/theorems/e072dcfb-1500-4155-8b3b-b1e683807727
-- title:
--   Butcher: pmul comm
-- statement:
--   The Butcher construction uses the pmul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L471-L477
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L471-L477

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

theorem RungeKuttaOrderConditions.Butcher.pmul_comm : ∀ u v : List ℚ, pmul u v = pmul v u
  := by sorry
