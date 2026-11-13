-- Prove2me | Theorems.Thm_Thm11SourceRoute_closedIntervalDarbouxAbsGapSmall_of_gapSmall
-- name    : Thm11SourceRoute.closedIntervalDarbouxAbsGapSmall_of_gapSmall
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:59:12.780037+00:00
-- url     : https://prove2.me/theorems/80d8f0ef-e30e-41dc-9612-bd0fcc436bb6
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000: Thm11SourceRoute.closedIntervalDarbouxAbsGapSmall_of_gapSmall
-- statement:
--   Source theorem `Thm11SourceRoute.closedIntervalDarbouxAbsGapSmall_of_gapSmall` extracted from `ProbabilityTheory.chapter_01.thm_1_1_darboux_gap`. The formal Lean declaration specifies the proposition.
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

theorem closedIntervalDarbouxAbsGapSmall_of_gapSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (hgap : ClosedIntervalDarbouxGapSmall a b f α) :
    ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
      P.mesh < δ →
        |upperSum P f α - lowerSum P f α| < eps := by
  sorry
end Thm11SourceRoute
end
