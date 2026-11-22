-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_targetFailureProbabilityReal_eq_coe
-- name    : PebblingLean.Hypercube.targetFailureProbabilityReal_eq_coe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:19.393326+00:00
-- url     : https://prove2.me/theorems/5c0244b0-273d-4d5c-92e8-d7f5090f9d47
-- title:
--   Hypercube: target Failure Probability Real eq coe
-- statement:
--   The Hypercube construction uses the target Failure Probability Real eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L944-L950
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L944-L950

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

theorem PebblingLean.Hypercube.targetFailureProbabilityReal_eq_coe {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) :
    targetFailureProbabilityReal (N := N) rIn rOut T target =
      (targetFailureProbability (N := N) rIn rOut T target : ℝ) := by sorry
