-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exp_target_sub_sampleTotalContribution
-- name    : PebblingLean.Hypercube.exp_target_sub_sampleTotalContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:29.811139+00:00
-- url     : https://prove2.me/theorems/07ac2656-acb9-43de-b827-39a0aeeadc1e
-- title:
--   Hypercube: exp target sub sample Total Contribution
-- statement:
--   The Hypercube construction uses the exp target sub sample Total Contribution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1224-L1238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1224-L1238

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

theorem PebblingLean.Hypercube.exp_target_sub_sampleTotalContribution
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n)
    (lam : ℝ) (sample : CenterSample n N) :
    Real.exp (lam * ((T : ℝ) -
        (sampleTotalContribution rIn rOut target sample : ℝ))) =
      Real.exp (lam * (T : ℝ)) *
        Real.exp (-(lam *
          (sampleTotalContribution rIn rOut target sample : ℝ))) := by sorry
