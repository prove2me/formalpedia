-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectation_eq_distance_sum
-- name    : PebblingLean.Hypercube.oneCenterContributionExpectation_eq_distance_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:49.533854+00:00
-- url     : https://prove2.me/theorems/34c43efe-7942-4fca-9316-7bc3d213ebdc
-- title:
--   Hypercube: one Center Contribution Expectation eq distance sum
-- statement:
--   Exact one-center expectation as a binomial sphere sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L226-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L226-L238

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability

theorem PebblingLean.Hypercube.oneCenterContributionExpectation_eq_distance_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectation rIn rOut target =
      ((∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i *
            if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ)) : ℚ) /
        (2 ^ n : ℚ) := by sorry
