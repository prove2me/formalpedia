-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusTotalContribution_toList
-- name    : PebblingLean.Hypercube.annulusTotalContribution_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:42.909038+00:00
-- url     : https://prove2.me/theorems/80bb8f74-45b9-4290-bdde-f42659510181
-- title:
--   Hypercube: annulus Total Contribution to List
-- statement:
--   The Hypercube construction uses the annulus Total Contribution to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L48-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L48-L54

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

theorem PebblingLean.Hypercube.annulusTotalContribution_toList {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (sample : CenterSample n N) :
    annulusTotalContribution rIn rOut target sample.toList =
      sampleTotalContribution rIn rOut target sample := by sorry
