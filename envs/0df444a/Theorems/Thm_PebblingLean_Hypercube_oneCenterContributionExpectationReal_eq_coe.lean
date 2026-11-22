-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectationReal_eq_coe
-- name    : PebblingLean.Hypercube.oneCenterContributionExpectationReal_eq_coe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:12.7297+00:00
-- url     : https://prove2.me/theorems/e04aa277-ccb3-4c87-a8df-d4b6e243f909
-- title:
--   Hypercube: one Center Contribution Expectation Real eq coe
-- statement:
--   The Hypercube construction uses the one Center Contribution Expectation Real eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L697-L702
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L697-L702

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

theorem PebblingLean.Hypercube.oneCenterContributionExpectationReal_eq_coe {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectationReal rIn rOut target =
      (oneCenterContributionExpectation rIn rOut target : ℝ) := by sorry
