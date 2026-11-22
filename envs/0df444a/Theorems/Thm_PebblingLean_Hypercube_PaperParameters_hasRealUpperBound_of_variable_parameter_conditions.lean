-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_variable_parameter_conditions
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_variable_parameter_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:23.081832+00:00
-- url     : https://prove2.me/theorems/162b5222-22c0-496c-92b1-1cf58d8e8ef2
-- title:
--   Paper Parameters: has Real Upper Bound of variable parameter conditions
-- statement:
--   Concrete parameter theorem using the paper-facing variable-demand product
--   recurrence.  For every recursive dimension `n` and every actual occupied pile
--   size `t ≥ minPile(splitM n)`, the probabilistic construction on the large
--   factor solves demand `t` with cost `t * costMultiplier n`.
--
--   This is the recurrence matching the proof in the paper.  The remaining
--   hypotheses are the concrete annulus mean, Bernstein/union-bound, fiber-cost,
--   integer cost, and normalized-cost estimates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2247-L2319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2247-L2319

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_variable_parameter_conditions
    {K A : ℝ} {n0 : ℕ} {costBound : ℕ → ℕ}
    {sampleCount : ℕ → ℕ → ℕ} {B : ℝ}
    (hn0_pos : 0 < n0)
    (hB : 0 ≤ B)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hbase_norm :
      ∀ n : ℕ, n < n0 → normalizedCost costBound n ≤ B)
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
