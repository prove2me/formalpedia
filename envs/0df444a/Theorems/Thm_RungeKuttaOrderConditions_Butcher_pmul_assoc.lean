-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_pmul_assoc
-- name    : RungeKuttaOrderConditions.Butcher.pmul_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:37.159512+00:00
-- url     : https://prove2.me/theorems/24ca3ee0-c668-46c9-8db7-04aefa4e1db5
-- title:
--   Butcher: pmul assoc
-- statement:
--   The Butcher construction uses the pmul assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L479-L485
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L479-L485

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

theorem RungeKuttaOrderConditions.Butcher.pmul_assoc : ∀ u v w : List ℚ, pmul (pmul u v) w = pmul u (pmul v w)
  := by sorry
