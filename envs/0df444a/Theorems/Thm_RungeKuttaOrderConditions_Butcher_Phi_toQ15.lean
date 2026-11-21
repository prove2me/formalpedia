-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_Phi_toQ15
-- name    : RungeKuttaOrderConditions.Butcher.Phi_toQ15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:51.622896+00:00
-- url     : https://prove2.me/theorems/782ace20-e4b5-42fd-b10a-448049d48a60
-- title:
--   Butcher: Phi to Q15
-- statement:
--   The elementary-weight engine commutes with the inclusion `toQ15` of `Z15` in `Q15`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L905-L910
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L905-L910

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

theorem RungeKuttaOrderConditions.Butcher.Phi_toQ15 (A : List (List Z15)) (b : List Z15) (t : RTree) :
    toQ15 (Phi A b t) = Phi (A.map (fun row => row.map toQ15)) (b.map toQ15) t := by sorry
