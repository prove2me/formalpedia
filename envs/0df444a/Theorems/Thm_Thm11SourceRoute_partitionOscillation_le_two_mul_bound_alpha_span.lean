-- Prove2me | Theorems.Thm_Thm11SourceRoute_partitionOscillation_le_two_mul_bound_alpha_span
-- name    : Thm11SourceRoute.partitionOscillation_le_two_mul_bound_alpha_span
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:57:23.705858+00:00
-- url     : https://prove2.me/theorems/90df2856-49d6-4aa6-9018-5e780eda07f0
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.partitionOscillation_le_two_mul_bound_alpha_span
-- statement:
--   Source theorem `Thm11SourceRoute.partitionOscillation_le_two_mul_bound_alpha_span` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F003
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem partitionOscillation_le_two_mul_bound_alpha_span
    {f α : ℝ → ℝ} {a b C : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    partitionOscillation P f α ≤ 2 * C * (α b - α a) := by sorry

end Thm11SourceRoute
