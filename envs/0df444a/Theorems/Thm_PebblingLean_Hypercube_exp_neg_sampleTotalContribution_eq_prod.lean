-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exp_neg_sampleTotalContribution_eq_prod
-- name    : PebblingLean.Hypercube.exp_neg_sampleTotalContribution_eq_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:27.350449+00:00
-- url     : https://prove2.me/theorems/5f18fe58-2579-4156-8abb-311918b3df1a
-- title:
--   Hypercube: exp neg sample Total Contribution eq prod
-- statement:
--   The Hypercube construction uses the exp neg sample Total Contribution eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1158-L1181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1158-L1181

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

theorem PebblingLean.Hypercube.exp_neg_sampleTotalContribution_eq_prod {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) (sample : CenterSample n N) :
    Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ))) =
      ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ))) := by sorry
