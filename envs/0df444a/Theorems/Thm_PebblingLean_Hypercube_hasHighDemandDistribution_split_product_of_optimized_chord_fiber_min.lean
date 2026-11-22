-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_optimized_chord_fiber_min
-- name    : PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:05:47.960844+00:00
-- url     : https://prove2.me/theorems/61eb190d-926f-4896-aa57-cda63e2ca30c
-- title:
--   Hypercube: has High Demand Distribution split product of optimized chord fiber min
-- statement:
--   Same recursive high-demand step, with the new pile-size invariant weakened
--   to any specified lower bound below `2^rOut`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L160-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L160-L180

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber_min
    {a m Tbase costBound S K N rIn rOut minNext : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos : 0 < gap)
    (hmean :
      (costBound : ℝ) + gap ≤
        (N : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost : N * 2 ^ rOut ≤ S * K)
    (hminNext : minNext ≤ 2 ^ rOut) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) minNext := by sorry
