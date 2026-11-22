-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_logLinearBudgets_logChernoff_sixLog_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_logLinearBudgets_logChernoff_sixLog_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:49.718623+00:00
-- url     : https://prove2.me/theorems/ccacbe90-2d19-4fac-af82-4981930c1718
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom log Linear Budgets log Chernoff six Log finite Base
-- statement:
--   Log-linear stack-budget wrapper.  The stack square-root side condition is
--   replaced by `16 log n≤n c^2`, where
--   `c=log(4/3)-log(2)/3`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4857-L4914
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L4857-L4914

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_logLinearBudgets_logChernoff_sixLog_finiteBase
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
    (hstackLogLinear :
      ∀ n : ℕ, n0 ≤ n →
        16 * Real.log (n : ℝ) ≤
          (n : ℝ) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) ^ 2)
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
