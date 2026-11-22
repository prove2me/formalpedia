-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_optimized_chord_annulusMean_log_of_mean_gap
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_log_of_mean_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:14.223807+00:00
-- url     : https://prove2.me/theorems/e3dc9a04-8c16-4dd8-9b2f-ebc01f1eba94
-- title:
--   Hypercube: has Solvable At Most Size of optimized chord annulus Mean log of mean gap
-- statement:
--   Costed high-demand conclusion with positivity of the mean derived from the
--   mean-gap hypothesis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1963-L1977
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1963-L1977

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_optimized_chord_annulusMean_log_of_mean_gap
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by sorry
