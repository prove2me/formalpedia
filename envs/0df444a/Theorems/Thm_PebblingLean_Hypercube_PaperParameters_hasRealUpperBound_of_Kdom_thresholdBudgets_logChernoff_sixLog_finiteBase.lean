-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_thresholdBudgets_logChernoff_sixLog_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_thresholdBudgets_logChernoff_sixLog_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:02.944569+00:00
-- url     : https://prove2.me/theorems/09556ca1-c260-4cc9-9d8a-1848fa6e90b6
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom threshold Budgets log Chernoff six Log finite Base
-- statement:
--   Same large-`n` wrapper, but the split budget is discharged by the explicit
--   quadratic cutoff `(128K^2)^2≤n0`, and the stack constant budget is discharged
--   by checking it once at `n0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4791-L4852
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4791-L4852

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_thresholdBudgets_logChernoff_sixLog_finiteBase
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
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
    (hwidthConst :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + 4 * Real.log 2 ≤
          (K / 30 * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hstackSqrt :
      ∀ n : ℕ, n0 ≤ n →
        4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
          (n : ℝ) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
