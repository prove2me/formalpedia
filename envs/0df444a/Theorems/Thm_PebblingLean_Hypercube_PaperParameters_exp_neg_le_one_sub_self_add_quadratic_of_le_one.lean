-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_exp_neg_le_one_sub_self_add_quadratic_of_le_one
-- name    : PebblingLean.Hypercube.PaperParameters.exp_neg_le_one_sub_self_add_quadratic_of_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:11.266319+00:00
-- url     : https://prove2.me/theorems/21e5142d-1e15-4294-84db-76a22df39915
-- title:
--   Paper Parameters: exp neg le one sub self add quadratic of le one
-- statement:
--   The matching bound for `exp(-x)` on `[0,1]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3451-L3483
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3451-L3483

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

theorem PebblingLean.Hypercube.PaperParameters.exp_neg_le_one_sub_self_add_quadratic_of_le_one {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x + (13 / 18) * x ^ 2 := by sorry
