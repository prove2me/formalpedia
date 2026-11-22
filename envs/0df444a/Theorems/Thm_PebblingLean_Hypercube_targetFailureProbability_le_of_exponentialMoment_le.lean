-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_targetFailureProbability_le_of_exponentialMoment_le
-- name    : PebblingLean.Hypercube.targetFailureProbability_le_of_exponentialMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:03.321353+00:00
-- url     : https://prove2.me/theorems/57acf46d-94d2-44fb-bce5-210c4f5e5dbc
-- title:
--   Hypercube: target Failure Probability le of exponential Moment le
-- statement:
--   The Hypercube construction uses the target Failure Probability le of exponential Moment le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1497-L1510
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1497-L1510

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

theorem PebblingLean.Hypercube.targetFailureProbability_le_of_exponentialMoment_le {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) {lam : ℝ} {eps : ℚ}
    (hlam : 0 < lam)
    (hmoment :
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤ (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps := by sorry
