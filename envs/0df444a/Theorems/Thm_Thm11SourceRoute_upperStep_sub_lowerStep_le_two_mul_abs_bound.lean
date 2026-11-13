-- Prove2me | Theorems.Thm_Thm11SourceRoute_upperStep_sub_lowerStep_le_two_mul_abs_bound
-- name    : Thm11SourceRoute.upperStep_sub_lowerStep_le_two_mul_abs_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:58:14.275321+00:00
-- url     : https://prove2.me/theorems/5fa384f7-2351-437b-b567-20abf910b3b9
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.upperStep_sub_lowerStep_le_two_mul_abs_bound
-- statement:
--   Source theorem `Thm11SourceRoute.upperStep_sub_lowerStep_le_two_mul_abs_bound` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem upperStep_sub_lowerStep_le_two_mul_abs_bound
    {f : ℝ → ℝ} {a b C : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    upperStep P f i - lowerStep P f i ≤ 2 * C := by sorry

end Thm11SourceRoute
