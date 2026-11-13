-- Prove2me | Theorems.Thm_Thm11SourceRoute_upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
-- name    : Thm11SourceRoute.upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:58:01.211216+00:00
-- url     : https://prove2.me/theorems/4794ca3d-f0f6-44b6-9150-92ced1105d5a
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
-- statement:
--   Source theorem `Thm11SourceRoute.upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ Partition.subinterval P i →
      ∀ y, y ∈ Partition.subinterval P i → |f x - f y| ≤ eta) :
    upperStep P f i - lowerStep P f i ≤ eta := by sorry

end Thm11SourceRoute
