-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_logBudgets_logChernoff_sixLog_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_logBudgets_logChernoff_sixLog_finiteBase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:13.996415+00:00
-- url     : https://prove2.me/theorems/eb9e920b-f534-41c1-971a-fc229fc6eb10
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom log Budgets log Chernoff six Log finite Base
-- statement:
--   Constant-domination version of the sqrt-margin wrapper.  It uses
--   `15A√3≤K` to reduce the width estimate to a residual
--   `(K/15)log(2)sqrt(n log n)` budget, and reduces the stack estimate to the
--   linear margin budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4583-L4639
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4583-L4639

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_logBudgets_logChernoff_sixLog_finiteBase
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
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
    (hwidthBudget :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + 3 * Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
            4 * Real.log (n : ℝ) ≤
          (K / 15 * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hstackBudget :
      ∀ n : ℕ, n0 ≤ n →
        2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
          ((3 : ℝ) * (n : ℝ) / 4) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
