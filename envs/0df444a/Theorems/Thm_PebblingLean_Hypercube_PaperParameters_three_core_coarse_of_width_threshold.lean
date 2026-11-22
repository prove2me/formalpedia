-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_core_coarse_of_width_threshold
-- name    : PebblingLean.Hypercube.PaperParameters.three_core_coarse_of_width_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:19.935669+00:00
-- url     : https://prove2.me/theorems/5b18cf1c-59bc-42b0-85b4-75fb815f58b3
-- title:
--   Paper Parameters: three core coarse of width threshold
-- statement:
--   A quadratic cutoff sufficient for the coarse annulus-width fit
--   `3(A sqrt(3n log n)+1)≤3n/4`.  This is the same split estimate with
--   the coefficient `A sqrt 3`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5420-L5449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5420-L5449

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

theorem PebblingLean.Hypercube.PaperParameters.three_core_coarse_of_width_threshold
    {A : ℝ} {n0 n : ℕ}
    (hA : 0 ≤ A)
    (hn0_growth : 58 ≤ n0)
    (hwidthFitThreshold : (128 * (A * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hn : n0 ≤ n) :
    3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) ≤
      (3 : ℝ) * (n : ℝ) / 4 := by sorry
