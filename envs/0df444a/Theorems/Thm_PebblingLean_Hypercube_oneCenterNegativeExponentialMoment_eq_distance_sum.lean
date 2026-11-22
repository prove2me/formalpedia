-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_eq_distance_sum
-- name    : PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_eq_distance_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:11.736522+00:00
-- url     : https://prove2.me/theorems/38680d9f-90bd-4476-8074-20704a303eeb
-- title:
--   Hypercube: one Center Negative Exponential Moment eq distance sum
-- statement:
--   Exact one-center negative exponential moment as a binomial Hamming-sphere
--   sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1134-L1147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1134-L1147

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

theorem PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_eq_distance_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    oneCenterNegativeExponentialMoment rIn rOut target lam =
      (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)))) /
        (2 ^ n : ℝ) := by sorry
