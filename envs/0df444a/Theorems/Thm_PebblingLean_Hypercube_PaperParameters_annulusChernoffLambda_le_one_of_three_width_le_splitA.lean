-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusChernoffLambda_le_one_of_three_width_le_splitA
-- name    : PebblingLean.Hypercube.PaperParameters.annulusChernoffLambda_le_one_of_three_width_le_splitA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:19.760803+00:00
-- url     : https://prove2.me/theorems/74a51848-486f-439c-9caa-f62aa58f365e
-- title:
--   Paper Parameters: annulus Chernoff Lambda le one of three width le split A
-- statement:
--   If `3w≤a`, then the standard Chernoff parameter
--   `λ=3w/(a+1)` is at most one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3544-L3554
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3544-L3554

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

theorem PebblingLean.Hypercube.PaperParameters.annulusChernoffLambda_le_one_of_three_width_le_splitA
    {A K : ℝ} {n : ℕ}
    (hwidth : 3 * annulusWidth A K n ≤ splitA K n) :
    annulusChernoffLambda A K n ≤ 1 := by sorry
