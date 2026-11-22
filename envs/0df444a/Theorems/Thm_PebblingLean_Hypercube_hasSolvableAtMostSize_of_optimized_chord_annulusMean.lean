-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_optimized_chord_annulusMean
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:44.721837+00:00
-- url     : https://prove2.me/theorems/2c3ca4d2-f2fd-4a56-b727-4ccdfabd0822
-- title:
--   Hypercube: has Solvable At Most Size of optimized chord annulus Mean
-- statement:
--   Costed high-demand conclusion from the optimized chord Chernoff estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1850-L1866
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1850-L1866

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean
    {n N rIn rOut T : ℕ} {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by sorry
