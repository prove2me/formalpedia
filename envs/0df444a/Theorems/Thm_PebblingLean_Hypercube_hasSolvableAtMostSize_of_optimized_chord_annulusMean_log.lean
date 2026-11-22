-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_optimized_chord_annulusMean_log
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_log
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:44.00781+00:00
-- url     : https://prove2.me/theorems/b8bd60ac-4da5-40ba-b616-33b521129ab5
-- title:
--   Hypercube: has Solvable At Most Size of optimized chord annulus Mean log
-- statement:
--   Costed high-demand conclusion from the optimized chord estimate and the
--   exponent condition `gap^2/(4 B_0 mu) ≥ (n+1) log 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1927-L1940
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1927-L1940

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_log
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by sorry
