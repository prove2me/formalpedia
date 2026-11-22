-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_bernoulli_third_right_log_le_quadratic
-- name    : PebblingLean.Hypercube.PaperParameters.bernoulli_third_right_log_le_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:17.640707+00:00
-- url     : https://prove2.me/theorems/af7ef5bd-0d12-4f3c-8461-f98f3d2e44c0
-- title:
--   Paper Parameters: bernoulli third right log le quadratic
-- statement:
--   Right Bernoulli log-moment bound used by the annulus Chernoff estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3509-L3529
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3509-L3529

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

theorem PebblingLean.Hypercube.PaperParameters.bernoulli_third_right_log_le_quadratic {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Real.log (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ≤
      lam / 3 + (13 / 54) * lam ^ 2 := by sorry
