-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_gauss_order6_rat
-- name    : RungeKuttaOrderConditions.Butcher.gauss_order6_rat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:58:39.548213+00:00
-- url     : https://prove2.me/theorems/882939db-837c-4a4a-9041-1279f3b52e22
-- title:
--   Butcher: gauss order6 rat
-- statement:
--   Gauss–Legendre s=3 satisfies ALL order-≤6 conditions over the true ℚ(√15)
--       tableau `gaussA`, `gaussB`: the full order-6 certificate, obtained from the
--       scaled integer certificate `gauss_order6` through the homogeneity bridge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L996-L1019
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L996-L1019

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

theorem RungeKuttaOrderConditions.Butcher.gauss_order6_rat : satisfiesOrderConditions gaussA gaussB 6 := by sorry
