-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_stackLogThreshold_of_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.explicit_stackLogThreshold_of_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:25.04639+00:00
-- url     : https://prove2.me/theorems/91d2959f-66d5-4725-a7d3-284accc212d4
-- title:
--   Paper Parameters: explicit stack Log Threshold of split Threshold
-- statement:
--   The stack logarithmic cutoff follows from the explicit split cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5669-L5687
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5669-L5687

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

theorem PebblingLean.Hypercube.PaperParameters.explicit_stackLogThreshold_of_splitThreshold {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ) := by sorry
