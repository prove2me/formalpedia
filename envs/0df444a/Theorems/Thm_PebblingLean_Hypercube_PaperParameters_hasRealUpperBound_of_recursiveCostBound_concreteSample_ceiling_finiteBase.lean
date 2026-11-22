-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:29.667153+00:00
-- url     : https://prove2.me/theorems/c2ba7386-5292-4d45-81b0-eb12b95c8ebe
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound concrete Sample ceiling finite Base
-- statement:
--   Same as
--   `hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_conditions`,
--   with the finite base constant chosen automatically as the sum of normalized
--   costs below the cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2673-L2713
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2673-L2713

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (t : ℝ) + demandGapForDemand n t ≤
            (sampleCountForDemand A K n t : ℝ) *
              (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (demandGapForDemand n t) ^ 2 /
              (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
                ((sampleCountForDemand A K n t : ℝ) *
                  (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hstack :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (2 ^ rOut A K n : ℝ) ≤
            (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n))
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
