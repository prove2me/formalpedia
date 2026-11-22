-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_standardLambda_noCeilSlack_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_standardLambda_noCeilSlack_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:28.91685+00:00
-- url     : https://prove2.me/theorems/538f0b39-3ebb-4e6f-aea5-44bea98f8125
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound standard Lambda no Ceil Slack finite Base
-- statement:
--   Standard-lambda wrapper with the ceiling slack fully discharged by the
--   explicit elementary threshold `n0≥58`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3812-L3846
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3812-L3846

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_standardLambda_noCeilSlack_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hsplitReal :
      ∀ n : ℕ, n0 ≤ n → (splitM K n : ℝ) ≤ (n : ℝ) / 4)
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
