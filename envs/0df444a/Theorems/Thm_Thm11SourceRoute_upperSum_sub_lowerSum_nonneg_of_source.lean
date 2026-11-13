-- Prove2me | Theorems.Thm_Thm11SourceRoute_upperSum_sub_lowerSum_nonneg_of_source
-- name    : Thm11SourceRoute.upperSum_sub_lowerSum_nonneg_of_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:58:37.639269+00:00
-- url     : https://prove2.me/theorems/5b67eae5-dc55-402e-8054-07c8ce23a5e6
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000: Thm11SourceRoute.upperSum_sub_lowerSum_nonneg_of_source
-- statement:
--   Source theorem `Thm11SourceRoute.upperSum_sub_lowerSum_nonneg_of_source` extracted from `ProbabilityTheory.chapter_01.thm_1_1_darboux_gap`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_darboux_gap.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem upperSum_sub_lowerSum_nonneg_of_source {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) :
    0 ≤ upperSum P f α - lowerSum P f α := by
  sorry
end Thm11SourceRoute
end
