-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:39.598803+00:00
-- url     : https://prove2.me/theorems/c21f98f6-b09c-4f99-87ea-3bc1278bb98c
-- title:
--   Paper Parameters: has Real Upper Bound of coarse Log Thresholds Knonneg standard Lambda tail Exponent finite Base
-- statement:
--   Coarsest current large-`n` wrapper.  The width and stack side conditions
--   now use only the envelope `sqrt(3n log n)` and the lower estimate
--   `splitM/5 ≥ K sqrt(n log n)/5 - 1`; the exact integer floors and ceilings are
--   handled internally.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4212-L4286
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4212-L4286

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
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
    (hwidthCoarse :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + (2 *
            (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
            Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          -4 * Real.log (n : ℝ) +
            (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2)
    (hstackCoarse :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 2 + 2 * Real.log (n : ℝ) +
            ((n : ℝ) / 3 +
                A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
              Real.log 2 ≤
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2 +
            ((3 : ℝ) * (n : ℝ) / 4) * Real.log ((4 : ℝ) / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
