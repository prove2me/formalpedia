-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_widthFitThreshold_of_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.explicit_widthFitThreshold_of_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:16.631862+00:00
-- url     : https://prove2.me/theorems/a14fe111-11ee-46b8-b45d-3e0536c2734d
-- title:
--   Paper Parameters: explicit width Fit Threshold of split Threshold
-- statement:
--   For the explicit constants `A=4`, `K=217`, the split cutoff is stronger
--   than the width-fit cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5560-L5583
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5560-L5583

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

theorem PebblingLean.Hypercube.PaperParameters.explicit_widthFitThreshold_of_splitThreshold {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    (128 * ((4 : ℝ) * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ) := by sorry
