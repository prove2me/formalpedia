-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_optimized_chord_fiber
-- name    : PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:34.333577+00:00
-- url     : https://prove2.me/theorems/dbb9d94f-e5f0-4bbd-a565-97a466f0a79c
-- title:
--   Hypercube: has High Demand Distribution split product of optimized chord fiber
-- statement:
--   Recursive high-demand step with an optimized-chord fiber construction.
--
--   An existing high-demand construction on `Q_m` supplies the demands.  The
--   optimized-chord construction on `Q_a` solves the largest possible demand
--   `costBound`, with fiber cost bounded by `S * K`; occupied-pile compression then
--   gives a high-demand distribution on `Q_(a+m)` with cost `costBound * K` and new
--   minimum pile size `2^rOut`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L130-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L130-L156

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

theorem PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber
    {a m Tbase costBound S K N rIn rOut : ℕ} {gap : ℝ}
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
    (hfiberCost : N * 2 ^ rOut ≤ S * K) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) (2 ^ rOut) := by sorry
