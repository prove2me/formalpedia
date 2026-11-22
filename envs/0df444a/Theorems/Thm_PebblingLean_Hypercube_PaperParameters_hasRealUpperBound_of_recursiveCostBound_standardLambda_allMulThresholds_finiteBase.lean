-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_standardLambda_allMulThresholds_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_standardLambda_allMulThresholds_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:33.195564+00:00
-- url     : https://prove2.me/theorems/5b6de20b-8c41-4492-b4f0-e963575ad903
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound standard Lambda all Mul Thresholds finite Base
-- statement:
--   Canonical-lambda version of the reduced wrapper.  This fixes both
--   Chernoff parameters to `3w/(a+1)`, leaving only the resulting two explicit
--   tail estimates and the deterministic growth thresholds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3769-L3808
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3769-L3808

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_standardLambda_allMulThresholds_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
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
            (((4 : ℝ) / 3) ^ splitA K n))
    (hceilHalf :
      ∀ n : ℕ, n0 ≤ n →
        (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ (n / 2))) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
