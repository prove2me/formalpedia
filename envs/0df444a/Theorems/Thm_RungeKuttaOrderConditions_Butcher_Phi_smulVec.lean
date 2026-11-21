-- Prove2me | Theorems.Thm_RungeKuttaOrderConditions_Butcher_Phi_smulVec
-- name    : RungeKuttaOrderConditions.Butcher.Phi_smulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:57:52.699602+00:00
-- url     : https://prove2.me/theorems/7c4b8f5c-cbfc-481a-8656-fa8f5e2ac774
-- title:
--   Butcher: Phi smul Vec
-- statement:
--   `Φ` is homogeneous of degree `|t|`: scaling the stage matrix and the weights
--       entrywise by `c` multiplies the elementary weight on `t` by `c ^ order t`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L967-L973
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean#L967-L973

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

theorem RungeKuttaOrderConditions.Butcher.Phi_smulVec (c : K) (A : List (List K)) (b : List K) (t : RTree) :
    Phi (smulMat c A) (smulVec c b) t = c ^ order t * Phi A b t := by sorry
