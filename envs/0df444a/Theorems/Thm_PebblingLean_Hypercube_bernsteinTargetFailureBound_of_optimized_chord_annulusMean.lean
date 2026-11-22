-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_bernsteinTargetFailureBound_of_optimized_chord_annulusMean
-- name    : PebblingLean.Hypercube.bernsteinTargetFailureBound_of_optimized_chord_annulusMean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:13.2466+00:00
-- url     : https://prove2.me/theorems/78f42658-feee-48b6-a334-bf5696f174d8
-- title:
--   Hypercube: bernstein Target Failure Bound of optimized chord annulus Mean
-- statement:
--   Target-failure bound with the target-independent real annulus mean
--   substituted for the fixed-target mean.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1661-L1692
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1661-L1692

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

theorem PebblingLean.Hypercube.bernsteinTargetFailureBound_of_optimized_chord_annulusMean
    {n N rIn rOut T : ℕ} {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (eps : ℝ)) :
    BernsteinTargetFailureBound n N rIn rOut T eps := by sorry
