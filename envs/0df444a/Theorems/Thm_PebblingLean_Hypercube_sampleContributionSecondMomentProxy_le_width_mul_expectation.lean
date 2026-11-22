-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sampleContributionSecondMomentProxy_le_width_mul_expectation
-- name    : PebblingLean.Hypercube.sampleContributionSecondMomentProxy_le_width_mul_expectation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:12.254278+00:00
-- url     : https://prove2.me/theorems/ed421cfa-97ac-4b88-9fea-5c73d4584d80
-- title:
--   Hypercube: sample Contribution Second Moment Proxy le width mul expectation
-- statement:
--   Bernstein variance-proxy bound: the sum of one-center second moments is at
--   most the annulus width factor times the mean total contribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L859-L877
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L859-L877

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

theorem PebblingLean.Hypercube.sampleContributionSecondMomentProxy_le_width_mul_expectation {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionSecondMomentProxy (N := N) rIn rOut target ≤
      (2 ^ (rOut - rIn) : ℚ) *
        sampleContributionExpectation (N := N) rIn rOut target := by sorry
