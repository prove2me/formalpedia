-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_simplifiedBernstein_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_simplifiedBernstein_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:38.334802+00:00
-- url     : https://prove2.me/theorems/3e405d02-9f22-4dcf-9ff3-fc1756c08d19
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound simplified Bernstein finite Base
-- statement:
--   Further reduced wrapper: the Bernstein/union-bound logarithmic hypothesis
--   is replaced by the paper-style pair of estimates `E X_t ≤ 2t` and
--   `(a+1)log 2 ≤ delta^2 t/(128 B_0)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2767-L2832
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2767-L2832

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_simplifiedBernstein_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hannulus :
      ∀ n : ℕ, n0 ≤ n →
        (1 - loss n / 8) * (2 ^ rOut A K n : ℝ) *
            (((3 : ℝ) / 4) ^ splitA K n) ≤
          (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hmeanUpper :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (sampleCountForDemand A K n t : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
              2 * (t : ℝ))
    (hlogSimple :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (loss n) ^ 2 * (t : ℝ) /
              (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ)))
    (hstackMin :
      ∀ n : ℕ, n0 ≤ n →
        (2 ^ rOut A K n : ℝ) ≤
          (loss n / 2) * (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
