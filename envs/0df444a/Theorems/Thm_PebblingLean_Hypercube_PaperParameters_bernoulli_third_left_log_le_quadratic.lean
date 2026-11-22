-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_bernoulli_third_left_log_le_quadratic
-- name    : PebblingLean.Hypercube.PaperParameters.bernoulli_third_left_log_le_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:24.13413+00:00
-- url     : https://prove2.me/theorems/a5d7f434-8001-4784-adf9-0f704ce14dab
-- title:
--   Paper Parameters: bernoulli third left log le quadratic
-- statement:
--   Left Bernoulli log-moment bound used by the annulus Chernoff estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3486-L3506
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3486-L3506

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

theorem PebblingLean.Hypercube.PaperParameters.bernoulli_third_left_log_le_quadratic {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Real.log (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ≤
      -lam / 3 + (13 / 54) * lam ^ 2 := by sorry
