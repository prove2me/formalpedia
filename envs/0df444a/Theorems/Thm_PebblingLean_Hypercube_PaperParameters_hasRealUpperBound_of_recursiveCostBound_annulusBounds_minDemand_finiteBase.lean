-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_annulusBounds_minDemand_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_annulusBounds_minDemand_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:47.987149+00:00
-- url     : https://prove2.me/theorems/bb3446d9-3f82-4f68-90d5-ccf89b3200ef
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound annulus Bounds min Demand finite Base
-- statement:
--   Current most reduced concrete upper-bound wrapper.  For the chosen paper
--   parameters it remains to prove, for all sufficiently large `n`, the concrete
--   dimension split, annulus lower/upper estimates, the minimum-demand Bernstein
--   threshold, stack-size threshold, pile-radius threshold, and ceiling slack.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2890-L2931
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2890-L2931

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_annulusBounds_minDemand_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hannulusLower :
      ∀ n : ℕ, n0 ≤ n →
        (1 - loss n / 8) * (2 ^ rOut A K n : ℝ) *
            (((3 : ℝ) / 4) ^ splitA K n) ≤
          (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hannulusUpper :
      ∀ n : ℕ, n0 ≤ n →
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
          (2 ^ rOut A K n : ℝ) * (((3 : ℝ) / 4) ^ splitA K n))
    (hlogMin :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
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
