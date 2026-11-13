-- Prove2me | Theorems.Thm_Thm11SourceRoute_upperSum_sub_lowerSum_eq_partitionOscillation
-- name    : Thm11SourceRoute.upperSum_sub_lowerSum_eq_partitionOscillation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:57:03.367466+00:00
-- url     : https://prove2.me/theorems/fe657535-505e-4fca-bed6-22305c134b40
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000: Thm11SourceRoute.upperSum_sub_lowerSum_eq_partitionOscillation
-- statement:
--   Source theorem `Thm11SourceRoute.upperSum_sub_lowerSum_eq_partitionOscillation` extracted from `ProbabilityTheory.chapter_01.thm_1_1_oscillation_basic`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) :
    upperSum P f α - lowerSum P f α =
      partitionOscillation P f α := by
  sorry
end Thm11SourceRoute
end
