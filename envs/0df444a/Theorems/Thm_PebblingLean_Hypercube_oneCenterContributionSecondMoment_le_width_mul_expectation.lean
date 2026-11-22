-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionSecondMoment_le_width_mul_expectation
-- name    : PebblingLean.Hypercube.oneCenterContributionSecondMoment_le_width_mul_expectation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:45.523978+00:00
-- url     : https://prove2.me/theorems/badc29a0-3a1f-4658-aedf-cc02a706148b
-- title:
--   Hypercube: one Center Contribution Second Moment le width mul expectation
-- statement:
--   Expectation-level version of `Z^2 ≤ B_0 Z` for one random annulus
--   contribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L102-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L102-L130

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

theorem PebblingLean.Hypercube.oneCenterContributionSecondMoment_le_width_mul_expectation {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionSecondMoment rIn rOut target ≤
      (2 ^ (rOut - rIn) : ℚ) * oneCenterContributionExpectation rIn rOut target := by sorry
