-- Prove2me | Theorems.Thm_Thm11SourceRoute_closedIntervalDarbouxGapSmall_of_oscillationSmall
-- name    : Thm11SourceRoute.closedIntervalDarbouxGapSmall_of_oscillationSmall
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:59:44.027301+00:00
-- url     : https://prove2.me/theorems/0f31dc13-0c2b-48eb-bc41-653634dc93e9
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000: Thm11SourceRoute.closedIntervalDarbouxGapSmall_of_oscillationSmall
-- statement:
--   Source theorem `Thm11SourceRoute.closedIntervalDarbouxGapSmall_of_oscillationSmall` extracted from `ProbabilityTheory.chapter_01.thm_1_1_darboux_gap`. The formal Lean declaration specifies the proposition.
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

theorem closedIntervalDarbouxGapSmall_of_oscillationSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hosc : ClosedIntervalDarbouxOscillationSmall a b f α) :
    ClosedIntervalDarbouxGapSmall a b f α := by
  sorry
end Thm11SourceRoute
end
