-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_bounds_of_isOptimalNumber
-- name    : PebblingLean.Hypercube.PaperParameters.explicit_bounds_of_isOptimalNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:13:27.652588+00:00
-- url     : https://prove2.me/theorems/a9adf90b-b23e-425a-aacd-1df308eca61d
-- title:
--   Paper Parameters: explicit bounds of is Optimal Number
-- statement:
--   Final packaged asymptotic bounds for any `k` certified as the optimal
--   pebbling number of `Q_n`: the formal lower bound and the explicit real upper
--   bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5786-L5795
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5786-L5795

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

theorem PebblingLean.Hypercube.PaperParameters.explicit_bounds_of_isOptimalNumber {n k : ℕ}
    (hopt : Pebbling.IsOptimalNumber (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) ∧
      (k : ℝ) ≤
        (Real.exp (4 * loss explicitCutoff) *
          finiteBaseNormalizedBound (recursiveCostBound 217 explicitCutoff)
            explicitCutoff) *
          (((4 : ℝ) / 3) ^ n) := by sorry
