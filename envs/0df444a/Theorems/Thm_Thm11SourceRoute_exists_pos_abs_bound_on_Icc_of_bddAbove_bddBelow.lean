-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
-- name    : Thm11SourceRoute.exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:57:49.502776+00:00
-- url     : https://prove2.me/theorems/bac77a3c-02ba-4acd-acbd-01060a688193
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
-- statement:
--   Source theorem `Thm11SourceRoute.exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by sorry

end Thm11SourceRoute
