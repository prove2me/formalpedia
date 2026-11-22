-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_targetFailureProbability_le_exp_optimized_chord
-- name    : PebblingLean.Hypercube.targetFailureProbability_le_exp_optimized_chord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:33.890666+00:00
-- url     : https://prove2.me/theorems/27610a07-59a1-4601-893d-09f4cc2f753a
-- title:
--   Hypercube: target Failure Probability le exp optimized chord
-- statement:
--   Fixed-target failure bound obtained from the optimized chord Chernoff
--   estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1524-L1560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1524-L1560

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

theorem PebblingLean.Hypercube.targetFailureProbability_le_exp_optimized_chord
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hmean :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) ≤
        (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps := by sorry
