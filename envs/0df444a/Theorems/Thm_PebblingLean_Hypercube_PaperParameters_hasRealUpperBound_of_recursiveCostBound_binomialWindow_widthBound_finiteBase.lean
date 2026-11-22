-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_binomialWindow_widthBound_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_binomialWindow_widthBound_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:51.765479+00:00
-- url     : https://prove2.me/theorems/2a9ca315-34ee-4a12-a59c-c366e5812056
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound binomial Window width Bound finite Base
-- statement:
--   Reduced wrapper with the annulus lower estimate stated as the concrete
--   binomial-window probability estimate for a `Binomial(splitA n, 1/3)` random
--   variable.  This isolates the remaining Chernoff-style estimate needed for the
--   annulus capture step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3021-L3057
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3021-L3057

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_binomialWindow_widthBound_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hwindow :
      ∀ n : ℕ, n0 ≤ n →
        1 - loss n / 8 ≤
          binomialWindowProbThird
            (splitA K n) (rIn A K n) (rOut A K n))
    (hlogWidth :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
            (128 * (2 ^ (2 * annulusWidth A K n) : ℝ)))
    (hstackMin :
      ∀ n : ℕ, n0 ≤ n →
        (2 ^ rOut A K n : ℝ) ≤
          (loss n / 2) * (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
