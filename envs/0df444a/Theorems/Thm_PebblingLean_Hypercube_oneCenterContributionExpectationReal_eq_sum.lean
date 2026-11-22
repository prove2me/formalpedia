-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterContributionExpectationReal_eq_sum
-- name    : PebblingLean.Hypercube.oneCenterContributionExpectationReal_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:42.362027+00:00
-- url     : https://prove2.me/theorems/03f85637-fe74-4507-88d0-3eeb28aa4c04
-- title:
--   Hypercube: one Center Contribution Expectation Real eq sum
-- statement:
--   The Hypercube construction uses the one Center Contribution Expectation Real eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L85-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L85-L90

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

theorem PebblingLean.Hypercube.oneCenterContributionExpectationReal_eq_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectationReal rIn rOut target =
      (∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℝ)) / (2 ^ n : ℝ) := by sorry
