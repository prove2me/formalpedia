-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:47.280478+00:00
-- url     : https://prove2.me/theorems/1cd19465-4acc-4561-87b1-6f93bb84379b
-- title:
--   Hypercube: has Solvable At Most Size of optimized chord annulus Mean inv two
-- statement:
--   Costed high-demand conclusion with fixed-target failure budget
--   `2^-(n+1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1890-L1905
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1890-L1905

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ)) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by sorry
