-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_explicitConstants_splitCutoff_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_splitCutoff_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:28.883804+00:00
-- url     : https://prove2.me/theorems/bfee6dda-206e-4bf7-9ddd-3af0af5b0fe2
-- title:
--   Paper Parameters: has Real Upper Bound of explicit Constants split Cutoff finite Base
-- statement:
--   Fully explicit upper-bound theorem with `A=4`, `K=217`, conditional only
--   on the split cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5711-L5731
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5711-L5731

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_splitCutoff_finiteBase
    {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound 217 n0) n0) := by sorry
