-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_normalizedCost_recursiveCostBound_step_of_ceiling
-- name    : PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:26.795805+00:00
-- url     : https://prove2.me/theorems/4e01a957-970e-48e0-8ee4-b6375f209c1d
-- title:
--   Paper Parameters: normalized Cost recursive Cost Bound step of ceiling
-- statement:
--   Normalized recurrence for the recursively defined integer cost bound after
--   absorbing the multiplier ceiling into a doubled loss term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2101-L2138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2101-L2138

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

theorem PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling
    {K : ℝ} {n0 n : ℕ}
    (hn : n0 ≤ n) (hsmall : splitM K n < n)
    (hslack : 1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    normalizedCost (recursiveCostBound K n0) n ≤
      (1 + 2 * loss n) *
        normalizedCost (recursiveCostBound K n0) (splitM K n) := by sorry
