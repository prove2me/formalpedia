-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_logLinearSplit_Knonneg_standardLambda_tailExponent_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_logLinearSplit_Knonneg_standardLambda_tailExponent_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:35.814692+00:00
-- url     : https://prove2.me/theorems/8ba78120-d35b-4383-b60d-4ebce5458ef6
-- title:
--   Paper Parameters: has Real Upper Bound of log Linear Split Knonneg standard Lambda tail Exponent finite Base
-- statement:
--   Same tail-exponent wrapper, but with the dimension split reduced to the
--   clean log-linear estimate `K^2 log n ≤ n/64`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3997-L4043
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3997-L4043

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_logLinearSplit_Knonneg_standardLambda_tailExponent_finiteBase
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hsplitLogLinear :
      ∀ n : ℕ, n0 ≤ n →
        K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64)
    (hleftExp :
      ∀ n : ℕ, n0 ≤ n →
        leftChernoffTerm A K (annulusChernoffLambda A K) n ≤
          Real.exp (-(tailExponent n)))
    (hrightExp :
      ∀ n : ℕ, n0 ≤ n →
        rightChernoffTerm A K (annulusChernoffLambda A K) n ≤
          Real.exp (-(tailExponent n)))
    (htailBudget :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 16 + 2 * Real.log (n : ℝ) ≤ tailExponent n)
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
