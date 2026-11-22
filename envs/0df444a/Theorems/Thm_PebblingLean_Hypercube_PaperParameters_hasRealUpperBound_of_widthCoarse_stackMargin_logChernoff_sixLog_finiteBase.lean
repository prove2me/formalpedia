-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_widthCoarse_stackMargin_logChernoff_sixLog_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_widthCoarse_stackMargin_logChernoff_sixLog_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:43.044733+00:00
-- url     : https://prove2.me/theorems/8ab3e8f3-d0b0-4e88-a06c-d2e19598518e
-- title:
--   Paper Parameters: has Real Upper Bound of width Coarse stack Margin log Chernoff six Log finite Base
-- statement:
--   Current strongest wrapper.  This uses the corrected stack margin
--   `log(4/3)-log(2)/3`, rather than the overly coarse replacement of `a/3` by
--   `n/3`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4427-L4518
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4427-L4518

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_widthCoarse_stackMargin_logChernoff_sixLog_finiteBase
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
    (hwidthCoarse :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + (2 *
            (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
            Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          -4 * Real.log (n : ℝ) +
            (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2)
    (hstackMargin :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 2 + 2 * Real.log (n : ℝ) +
            (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
              Real.log 2 ≤
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2 +
            ((3 : ℝ) * (n : ℝ) / 4) *
              (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
