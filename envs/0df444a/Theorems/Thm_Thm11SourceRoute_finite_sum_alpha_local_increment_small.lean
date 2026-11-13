-- Prove2me | Theorems.Thm_Thm11SourceRoute_finite_sum_alpha_local_increment_small
-- name    : Thm11SourceRoute.finite_sum_alpha_local_increment_small
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:26:53.195065+00:00
-- url     : https://prove2.me/theorems/140305fb-a17e-4052-87c1-d1835732f3c7
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.finite_sum_alpha_local_increment_small
-- statement:
--   Source theorem `Thm11SourceRoute.finite_sum_alpha_local_increment_small` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F002
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem finite_sum_alpha_local_increment_small {α : ℝ → ℝ}
    (S : Finset ℝ)
    (hα : ∀ c : ℝ, c ∈ S → ContinuousAt α c)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ → ℝ,
      (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
      (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by sorry

end Thm11SourceRoute
