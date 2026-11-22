-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
-- name    : PebblingLean.Hypercube.hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:10.302333+00:00
-- url     : https://prove2.me/theorems/1178fd97-a1ca-4743-9580-7e2c08d1bc35
-- title:
--   Hypercube: has High Demand Distribution of optimized chord annulus Mean log of mean gap
-- statement:
--   High-demand conclusion from the optimized chord estimate and logarithmic
--   union-bound criterion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1981-L2020
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1981-L2020

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

theorem PebblingLean.Hypercube.hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasHighDemandDistribution n T (N * 2 ^ rOut) (2 ^ rOut) := by sorry
