-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_le_exp_optimized_chord
-- name    : PebblingLean.Hypercube.targetLowerTailExponentialMoment_le_exp_optimized_chord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:34.120328+00:00
-- url     : https://prove2.me/theorems/faa1eee1-e40e-4b5c-b09f-95e363a509c2
-- title:
--   Hypercube: target Lower Tail Exponential Moment le exp optimized chord
-- statement:
--   Optimized chord-based Chernoff bound for one fixed target.  This is the
--   analytic gap-closing statement: if the expected annulus contribution `mu`
--   exceeds the threshold by `gap`, then the optimized exponential moment is
--   bounded by `exp(-gap^2/(4 B mu))`, where `B = 2^(rOut-rIn)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1341-L1432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1341-L1432

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

theorem PebblingLean.Hypercube.targetLowerTailExponentialMoment_le_exp_optimized_chord
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {gap : ℝ}
    (hgap : 0 ≤ gap)
    (hmu_pos :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hmean :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target
        (gap /
          (2 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target))) ≤
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by sorry
