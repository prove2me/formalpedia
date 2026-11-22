-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_exp_neg_sampleTotalContribution_eq_pow
-- name    : PebblingLean.Hypercube.sum_exp_neg_sampleTotalContribution_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:29.218142+00:00
-- url     : https://prove2.me/theorems/f6772778-4a35-412d-968c-35091d022e04
-- title:
--   Hypercube: sum exp neg sample Total Contribution eq pow
-- statement:
--   The Hypercube construction uses the sum exp neg sample Total Contribution eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1201-L1222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1201-L1222

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

theorem PebblingLean.Hypercube.sum_exp_neg_sampleTotalContribution_eq_pow {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ sample : CenterSample n N,
      Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ)))) =
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by sorry
