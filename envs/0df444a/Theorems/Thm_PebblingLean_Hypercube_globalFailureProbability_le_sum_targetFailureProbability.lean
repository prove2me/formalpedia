-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_globalFailureProbability_le_sum_targetFailureProbability
-- name    : PebblingLean.Hypercube.globalFailureProbability_le_sum_targetFailureProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:15.063657+00:00
-- url     : https://prove2.me/theorems/26b93ef6-28c5-4f8f-a2dc-bc46020ef79a
-- title:
--   Hypercube: global Failure Probability le sum target Failure Probability
-- statement:
--   Union bound over all targets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1568-L1585
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1568-L1585

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

theorem PebblingLean.Hypercube.globalFailureProbability_le_sum_targetFailureProbability {n N rIn rOut T : ℕ} :
    globalFailureProbability (n := n) (N := N) rIn rOut T ≤
      ∑ target : HypercubeVertex n,
        targetFailureProbability (N := N) rIn rOut T target := by sorry
