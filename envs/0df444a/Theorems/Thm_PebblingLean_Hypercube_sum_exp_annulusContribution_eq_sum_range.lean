-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_exp_annulusContribution_eq_sum_range
-- name    : PebblingLean.Hypercube.sum_exp_annulusContribution_eq_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:24.638922+00:00
-- url     : https://prove2.me/theorems/1ddd18c7-2be2-4aeb-be14-fbebbbd3c3e3
-- title:
--   Hypercube: sum exp annulus Contribution eq sum range
-- statement:
--   Exact one-center negative exponential moment numerator, grouped by Hamming
--   distance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1088-L1130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1088-L1130

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

theorem PebblingLean.Hypercube.sum_exp_annulusContribution_eq_sum_range {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by sorry
