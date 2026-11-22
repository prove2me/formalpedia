-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_annulusContribution_eq_sum_range
-- name    : PebblingLean.Hypercube.sum_annulusContribution_eq_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:45.402825+00:00
-- url     : https://prove2.me/theorems/befcd813-f418-4cd7-991f-018f9a35f6f6
-- title:
--   Hypercube: sum annulus Contribution eq sum range
-- statement:
--   Exact one-center annulus contribution, grouped by Hamming distance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L188-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L188-L223

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

theorem PebblingLean.Hypercube.sum_annulusContribution_eq_sum_range {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    (∑ center : HypercubeVertex n, annulusContribution rIn rOut target center) =
      ∑ i ∈ Finset.range (n + 1),
        Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 := by sorry
