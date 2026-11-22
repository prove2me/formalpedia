-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_highDemandDistribution_of_recursive_split_schedule
-- name    : PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:33.743864+00:00
-- url     : https://prove2.me/theorems/2aae8c0a-f198-4ebf-b23d-4a25680aba82
-- title:
--   Hypercube: high Demand Distribution of recursive split schedule
-- statement:
--   Abstract recursive split schedule for the upper bound.
--
--   For every large dimension `n`, the schedule chooses a split
--   `Q_n ≃ Q_{splitA n} □ Q_{splitM n}`.  The inductive hypothesis supplies the
--   base high-demand distribution on `Q_{splitM n}`; the optimized-chord annulus
--   construction supplies the fiber distribution on `Q_{splitA n}` for demand
--   `costBound (splitM n)`.  The hypotheses here are exactly the numerical
--   conditions that remain after all graph-theoretic, probabilistic, and product
--   bookkeeping has been formalized.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L233-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L233-L285

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

theorem PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase :
      ∀ n : ℕ, n < n0 →
        HasHighDemandDistribution n 1 (costBound n) (minPile n))
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) := by sorry
