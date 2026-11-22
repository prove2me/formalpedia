-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sampleContributionExpectation_eq_nat_mul_oneCenter
-- name    : PebblingLean.Hypercube.sampleContributionExpectation_eq_nat_mul_oneCenter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:15.404977+00:00
-- url     : https://prove2.me/theorems/a1f33359-f6cd-4ab4-8ece-fb7f211476d8
-- title:
--   Hypercube: sample Contribution Expectation eq nat mul one Center
-- statement:
--   Linearity of expectation for the independent uniform center tuple used
--   here: the expected total contribution is `N` times the one-center expectation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L833-L848
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L833-L848

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

theorem PebblingLean.Hypercube.sampleContributionExpectation_eq_nat_mul_oneCenter {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionExpectation (N := N) rIn rOut target =
      (N : ℚ) * oneCenterContributionExpectation rIn rOut target := by sorry
