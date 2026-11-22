-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_chernoffTails_widthBound_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_chernoffTails_widthBound_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:01.607553+00:00
-- url     : https://prove2.me/theorems/5b46a559-0ed2-4ab1-ae8a-507517bbdf10
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound chernoff Tails width Bound finite Base
-- statement:
--   Chernoff-parameter form of the reduced upper-bound wrapper.  It remains
--   to choose nonnegative parameters for the two binomial tails and verify the
--   displayed explicit exponential bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3103-L3151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3103-L3151

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_chernoffTails_widthBound_finiteBase
    {K A : ℝ} {n0 : ℕ} {lamLeft lamRight : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hlamLeft :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamLeft n)
    (hlamRight :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamRight n)
    (hchernoff :
      ∀ n : ℕ, n0 ≤ n →
        Real.exp (lamLeft n * (rIn A K n : ℝ)) *
            (((1 : ℝ) / 3) * Real.exp (-(lamLeft n)) + ((2 : ℝ) / 3)) ^
              splitA K n +
          Real.exp (-(lamRight n * (rOut A K n : ℝ))) *
            (((1 : ℝ) / 3) * Real.exp (lamRight n) + ((2 : ℝ) / 3)) ^
              splitA K n ≤
        loss n / 8)
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
