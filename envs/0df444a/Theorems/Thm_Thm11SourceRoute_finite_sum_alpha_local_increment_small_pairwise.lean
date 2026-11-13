-- Prove2me | Theorems.Thm_Thm11SourceRoute_finite_sum_alpha_local_increment_small_pairwise
-- name    : Thm11SourceRoute.finite_sum_alpha_local_increment_small_pairwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:27:20.051621+00:00
-- url     : https://prove2.me/theorems/fbf56aa0-79b7-4f87-8a6c-4a1f0090d9a7
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.finite_sum_alpha_local_increment_small_pairwise
-- statement:
--   Source theorem `Thm11SourceRoute.finite_sum_alpha_local_increment_small_pairwise` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem finite_sum_alpha_local_increment_small_pairwise
    {α : ℝ → ℝ}
    (S : Finset ℝ)
    (hα_mono : Monotone α)
    (hα : ∀ c : ℝ, c ∈ S → ContinuousAt α c)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ → ℝ,
      (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
      (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps ∧
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by sorry

end Thm11SourceRoute
