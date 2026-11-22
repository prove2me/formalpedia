-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_variable_conditions
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_variable_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:29.393956+00:00
-- url     : https://prove2.me/theorems/00a892f8-04a5-4a19-9554-32f5089fe7df
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound variable conditions
-- statement:
--   Variable-demand specialization to the recursively defined integer cost
--   bound.  This is the closest formal wrapper to the paper's recursive
--   construction currently in the project.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2486-L2533
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2486-L2533

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_variable_conditions
    {K A : ℝ} {n0 : ℕ} {sampleCount : ℕ → ℕ → ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost (recursiveCostBound K n0) n ≤ B)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (t : ℝ) + demandGapForDemand n t ≤
            (sampleCount n t : ℝ) *
              (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (demandGapForDemand n t) ^ 2 /
              (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
                ((sampleCount n t : ℝ) *
                  (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          sampleCount n t * 2 ^ rOut A K n ≤ t * costMultiplier K n)
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hcostReal :
      ∀ n : ℕ, n0 ≤ n →
        (recursiveCostBound K n0 n : ℝ) ≤
          (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
            (recursiveCostBound K n0 (splitM K n) : ℝ)) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * loss n0) * B) := by sorry
