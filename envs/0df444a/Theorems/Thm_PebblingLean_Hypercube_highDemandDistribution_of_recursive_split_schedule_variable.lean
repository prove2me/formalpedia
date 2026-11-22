-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_highDemandDistribution_of_recursive_split_schedule_variable
-- name    : PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule_variable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:36.67506+00:00
-- url     : https://prove2.me/theorems/9be449de-1535-45b4-8bf3-d513f36aa2ba
-- title:
--   Hypercube: high Demand Distribution of recursive split schedule variable
-- statement:
--   Paper-accurate recursive split schedule with variable fiber demand.
--
--   The fixed-demand schedule above asks the `Q_a` fiber construction to solve the
--   maximum possible pile size in every occupied fiber.  The paper instead applies
--   the high-demand lemma separately to each occupied pile size `t`; this theorem
--   packages that sharper recurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L293-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L293-L351

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

theorem PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule_variable
    {costBound minPile splitA splitM K rIn rOut : ℕ → ℕ}
    {N : ℕ → ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {n0 : ℕ}
    (hbase :
      ∀ n : ℕ, n < n0 →
        HasHighDemandDistribution n 1 (costBound n) (minPile n))
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
