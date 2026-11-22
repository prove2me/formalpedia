-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_coreSplit_standardLambda_noCeilSlack_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_coreSplit_standardLambda_noCeilSlack_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:32.752802+00:00
-- url     : https://prove2.me/theorems/cc210a71-3465-4a7a-82af-f83621cc55d5
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound core Split standard Lambda no Ceil Slack finite Base
-- statement:
--   Same standard-lambda wrapper, with the split estimate reduced to the
--   ceiling-core inequality `K sqrt(n log n)+1 ≤ n/4`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3850-L3891
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3850-L3891

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_coreSplit_standardLambda_noCeilSlack_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hsplitCore_nonneg :
      ∀ n : ℕ, n0 ≤ n →
        0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hsplitCore :
      ∀ n : ℕ, n0 ≤ n →
        K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
          (n : ℝ) / 4)
    (hleftMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * leftChernoffTerm A K (annulusChernoffLambda A K) n ≤ loss n)
    (hrightMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * rightChernoffTerm A K (annulusChernoffLambda A K) n ≤ loss n)
    (hlogWidthMul :
      ∀ n : ℕ, n0 ≤ n →
        128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
            (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ))
    (hstackMul :
      ∀ n : ℕ, n0 ≤ n →
        2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
          (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
