-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_coreLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coreLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:11.17361+00:00
-- url     : https://prove2.me/theorems/6a6c0d2e-c8a2-400e-a015-1563bbcb39fd
-- title:
--   Paper Parameters: has Real Upper Bound of core Log Thresholds Knonneg standard Lambda tail Exponent finite Base
-- statement:
--   Same log-threshold wrapper with the annulus-width ceiling isolated.  The
--   width and stack hypotheses use the real core
--   `A sqrt(a log(2n^2)) + 1`, which is the form expected for the remaining
--   large-`n` analytic estimates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4151-L4206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4151-L4206

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coreLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
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
    (hwidthCoreLog :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + (2 * (annulusWidthCore A K n + 1)) *
            Real.log 2 +
            Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          -4 * Real.log (n : ℝ) +
            ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2)
    (hstackCoreLog :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 2 + 2 * Real.log (n : ℝ) +
            (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
              Real.log 2 ≤
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
            (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
