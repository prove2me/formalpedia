-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_phiForest_perm
-- name    : RungeKuttaOrderConditions.Butcher.phiForest_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:39.37616+00:00
-- url     : https://prove2.me/theorems/34ea1e06-35f5-4278-bd58-2af2ef7b9529
-- title:
--   Butcher: phi Forest perm
-- statement:
--   The Butcher construction uses the phi Forest perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L487-L497
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L487-L497

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

theorem RungeKuttaOrderConditions.Butcher.phiForest_perm (A : List (List ℚ)) {F G : Forest} (h : F.Perm G) :
    phiForest A F = phiForest A G := by sorry
