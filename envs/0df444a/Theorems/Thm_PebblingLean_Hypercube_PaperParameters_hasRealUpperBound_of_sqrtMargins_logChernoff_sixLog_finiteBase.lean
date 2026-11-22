-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_sqrtMargins_logChernoff_sixLog_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_sqrtMargins_logChernoff_sixLog_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:43.022614+00:00
-- url     : https://prove2.me/theorems/dc334641-9248-43ca-abb1-9ea3053a2f24
-- title:
--   Paper Parameters: has Real Upper Bound of sqrt Margins log Chernoff six Log finite Base
-- statement:
--   Sqrt-coefficient version of the current strongest wrapper.  The remaining
--   width and stack estimates are now stated with explicit coefficients multiplying
--   `sqrt(n log n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4523-L4577
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4523-L4577

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_sqrtMargins_logChernoff_sixLog_finiteBase
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hsplitLogLinear :
      ∀ n : ℕ, n0 ≤ n →
        K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64)
    (hleftLog :
      ∀ n : ℕ, n0 ≤ n →
        annulusChernoffLambda A K n * (rIn A K n : ℝ) +
            (splitA K n : ℝ) *
              Real.log (((1 : ℝ) / 3) *
                  Real.exp (-(annulusChernoffLambda A K n)) +
                ((2 : ℝ) / 3)) ≤ -(tailExponent n))
    (hrightLog :
      ∀ n : ℕ, n0 ≤ n →
        -(annulusChernoffLambda A K n * (rOut A K n : ℝ)) +
            (splitA K n : ℝ) *
              Real.log (((1 : ℝ) / 3) *
                  Real.exp (annulusChernoffLambda A K n) +
                ((2 : ℝ) / 3)) ≤ -(tailExponent n))
    (htailSix :
      ∀ n : ℕ, n0 ≤ n →
        6 * Real.log (n : ℝ) ≤ tailExponent n)
    (hwidthSqrt :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + 3 * Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
            4 * Real.log (n : ℝ) ≤
          ((K / 5 - 2 * A * Real.sqrt 3) * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hstackSqrt :
      ∀ n : ℕ, n0 ≤ n →
        2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
          ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
              Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
            ((3 : ℝ) * (n : ℝ) / 4) *
              (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
