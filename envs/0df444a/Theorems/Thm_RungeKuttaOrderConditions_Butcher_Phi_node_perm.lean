-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_Phi_node_perm
-- name    : RungeKuttaOrderConditions.Butcher.Phi_node_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:39.753588+00:00
-- url     : https://prove2.me/theorems/11085787-2312-4a84-b8b8-dbadb1a3aa09
-- title:
--   Butcher: Phi node perm
-- statement:
--   Φ is invariant under permuting the children of the root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L514-L516
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L514-L516

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

theorem RungeKuttaOrderConditions.Butcher.Phi_node_perm (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    Phi A b (.node F) = Phi A b (.node G) := by sorry
