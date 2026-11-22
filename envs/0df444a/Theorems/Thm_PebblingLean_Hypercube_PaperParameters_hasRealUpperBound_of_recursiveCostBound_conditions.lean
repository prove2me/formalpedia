-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_conditions
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:12:39.531278+00:00
-- url     : https://prove2.me/theorems/0ef53d22-3ca0-4f5d-8114-5ca0afbd4609
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound conditions
-- statement:
--   Specialization of the concrete parameter theorem to the recursively
--   defined integer cost bound.  The finite base cost and the integer product
--   recurrence are discharged by `recursiveCostBound_base_cost` and
--   `recursiveCostBound_step_cost`; the remaining hypotheses are the genuine
--   analytic estimates for the chosen annulus, sample count, and ceiling overhead
--   in the real normalized recurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2379-L2429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2379-L2429

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_conditions
    {K A : ℝ} {n0 : ℕ} {sampleCount : ℕ → ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost (recursiveCostBound K n0) n ≤ B)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        0 < demandGap K (recursiveCostBound K n0) n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (recursiveCostBound K n0 (splitM K n) : ℝ) +
            demandGap K (recursiveCostBound K n0) n ≤
          (sampleCount n : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (demandGap K (recursiveCostBound K n0) n) ^ 2 /
            (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
              ((sampleCount n : ℝ) *
                (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        sampleCount n * 2 ^ rOut A K n ≤
          minPile (splitM K n) * costMultiplier K n)
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hcostReal :
      ∀ n : ℕ, n0 ≤ n →
        (recursiveCostBound K n0 n : ℝ) ≤
          (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
            (recursiveCostBound K n0 (splitM K n) : ℝ)) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * loss n0) * B) := by sorry
