-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_filter_dist_eq_exp_annulusContribution
-- name    : PebblingLean.Hypercube.sum_filter_dist_eq_exp_annulusContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:19.793002+00:00
-- url     : https://prove2.me/theorems/6b7e0ec8-4b3f-4f36-9e6a-72ef596c44b0
-- title:
--   Hypercube: sum filter dist eq exp annulus Contribution
-- statement:
--   Sum of the one-center negative exponential factor over one Hamming sphere.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1036-L1084
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1036-L1084

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

theorem PebblingLean.Hypercube.sum_filter_dist_eq_exp_annulusContribution {n rIn rOut i : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) =
      (Nat.choose n i : ℝ) *
        Real.exp
          (-(lam *
            ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by sorry
