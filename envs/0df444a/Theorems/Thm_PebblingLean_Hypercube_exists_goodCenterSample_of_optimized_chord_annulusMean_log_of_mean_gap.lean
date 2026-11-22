-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_optimized_chord_annulusMean_log_of_mean_gap
-- name    : PebblingLean.Hypercube.exists_goodCenterSample_of_optimized_chord_annulusMean_log_of_mean_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:15.624024+00:00
-- url     : https://prove2.me/theorems/1e04a67a-280e-442e-aa52-25b048a8fa96
-- title:
--   Hypercube: exists good Center Sample of optimized chord annulus Mean log of mean gap
-- statement:
--   The same log-threshold finish, deriving positivity of the mean from the
--   positive gap and the inequality `T + gap ≤ mean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1944-L1959
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1944-L1959

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

theorem PebblingLean.Hypercube.exists_goodCenterSample_of_optimized_chord_annulusMean_log_of_mean_gap
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by sorry
