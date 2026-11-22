-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_exp_le_one_add_self_add_quadratic_of_le_one
-- name    : PebblingLean.Hypercube.PaperParameters.exp_le_one_add_self_add_quadratic_of_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:07.526807+00:00
-- url     : https://prove2.me/theorems/e1fa96c1-dae0-465c-91a5-d56bc2185fe9
-- title:
--   Paper Parameters: exp le one add self add quadratic of le one
-- statement:
--   A coarse second-order exponential upper bound on `[0,1]`.  The constant
--   `13/18` comes from the third-order Taylor bound in mathlib and is deliberately
--   not optimized.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3424-L3448
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3424-L3448

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters

theorem PebblingLean.Hypercube.PaperParameters.exp_le_one_add_self_add_quadratic_of_le_one {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + (13 / 18) * x ^ 2 := by sorry
