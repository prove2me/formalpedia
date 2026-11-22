-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sampleContributionExpectation_eq_sum
-- name    : PebblingLean.Hypercube.sampleContributionExpectation_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:09.665858+00:00
-- url     : https://prove2.me/theorems/17e83fbf-63fe-486d-9aba-08c7d65441d4
-- title:
--   Hypercube: sample Contribution Expectation eq sum
-- statement:
--   The Hypercube construction uses the sample Contribution Expectation eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L725-L731
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L725-L731

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

theorem PebblingLean.Hypercube.sampleContributionExpectation_eq_sum {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionExpectation (N := N) rIn rOut target =
      (∑ sample : CenterSample n N,
          (sampleTotalContribution rIn rOut target sample : ℚ)) /
        (Fintype.card (CenterSample n N) : ℚ) := by sorry
