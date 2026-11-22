-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base
-- name    : PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:38.687681+00:00
-- url     : https://prove2.me/theorems/7fa419cb-4e24-4a1d-a40b-c5d35e99eed5
-- title:
--   Hypercube: high Demand Distribution of recursive split schedule variable large constant base
-- statement:
--   Variable-demand recursive split schedule, with finite base cases discharged
--   by the constant distribution having the requested minimum pile size on every
--   vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L445-L489
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L445-L489

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

theorem PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base
    {costBound minPile splitA splitM K rIn rOut : ℕ → ℕ}
    {N : ℕ → ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t → 0 < gap n t)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          (t : ℝ) + gap n t ≤
            (N n t : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (gap n t) ^ 2 /
              (4 * (2 ^ (rOut n - rIn n) : ℝ) *
                ((N n t : ℝ) *
                  (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          N n t * 2 ^ rOut n ≤ t * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) := by sorry
