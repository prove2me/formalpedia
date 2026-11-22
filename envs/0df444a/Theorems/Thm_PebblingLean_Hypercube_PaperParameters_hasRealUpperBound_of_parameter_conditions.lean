-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_parameter_conditions
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_parameter_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:25.126858+00:00
-- url     : https://prove2.me/theorems/86a6d722-5da1-4b1b-94db-066a00e35967
-- title:
--   Paper Parameters: has Real Upper Bound of parameter conditions
-- statement:
--   The concrete parameter theorem.  The hypotheses are the remaining
--   numerical estimates for the paper's chosen schedule.  Everything after those
--   estimates is now formal: the high-demand construction, product recursion, base
--   cases, normalized loss control, and final real `C(4/3)^n` upper bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2171-L2237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2171-L2237

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_parameter_conditions
    {K A : ℝ} {n0 : ℕ} {costBound sampleCount : ℕ → ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost costBound n ≤ B)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < demandGap K costBound n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM K n) : ℝ) + demandGap K costBound n ≤
          (sampleCount n : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (demandGap K costBound n) ^ 2 /
            (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
              ((sampleCount n : ℝ) *
                (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        sampleCount n * 2 ^ rOut A K n ≤
          minPile (splitM K n) * costMultiplier K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM K n) * costMultiplier K n ≤ costBound n)
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hnormStep :
      ∀ n : ℕ, n0 ≤ n →
        normalizedCost costBound n ≤
          (1 + loss n) * normalizedCost costBound (splitM K n)) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * loss n0) * B) := by sorry
