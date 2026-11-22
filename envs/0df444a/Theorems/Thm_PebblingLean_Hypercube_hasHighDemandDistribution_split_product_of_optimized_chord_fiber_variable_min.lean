-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_optimized_chord_fiber_variable_min
-- name    : PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber_variable_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:32.965037+00:00
-- url     : https://prove2.me/theorems/0009b025-9ad5-4082-a1fd-4f15cc4f3fb0
-- title:
--   Hypercube: has High Demand Distribution split product of optimized chord fiber variable min
-- statement:
--   Variable-demand version of the optimized-chord product step.
--
--   For every occupied pile size `t ≥ S` in the recursive `Q_m` distribution, the
--   optimized-chord construction supplies a `t`-solvable fiber in `Q_a` of cost
--   `t*K`.  This is the recurrence used in the paper: costs add as
--   `∑_z E z * K = |E|*K`, rather than paying for a worst-case demand in every
--   occupied fiber.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L189-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L189-L222

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

theorem PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber_variable_min
    {a m Tbase costBound S K rIn rOut minNext : ℕ}
    {N : ℕ → ℕ} {gap : ℕ → ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos :
      ∀ t : ℕ, S ≤ t → 0 < gap t)
    (hmean :
      ∀ t : ℕ, S ≤ t →
        (t : ℝ) + gap t ≤
          (N t : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ∀ t : ℕ, S ≤ t →
        ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap t) ^ 2 /
            (4 * (2 ^ (rOut - rIn) : ℝ) *
              ((N t : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost :
      ∀ t : ℕ, S ≤ t → N t * 2 ^ rOut ≤ t * K)
    (hminNext : minNext ≤ 2 ^ rOut) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) minNext := by sorry
