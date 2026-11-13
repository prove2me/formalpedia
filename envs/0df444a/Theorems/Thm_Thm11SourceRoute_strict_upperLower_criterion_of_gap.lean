-- Prove2me | Theorems.Thm_Thm11SourceRoute_strict_upperLower_criterion_of_gap
-- name    : Thm11SourceRoute.strict_upperLower_criterion_of_gap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:08:56.403949+00:00
-- url     : https://prove2.me/theorems/70d2982f-3097-4893-88c4-c80460c6a555
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001: Thm11SourceRoute.strict_upperLower_criterion_of_gap
-- statement:
--   Source theorem `Thm11SourceRoute.strict_upperLower_criterion_of_gap` extracted from `ProbabilityTheory.chapter_01.thm_1_1_common_limit`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_limit.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_darboux_gap_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_finite_discontinuity_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem strict_upperLower_criterion_of_gap
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromGap)
    (hosc : StrictFiniteDiscontinuityOscillationCriterion) :
    StrictFiniteDiscontinuityUpperLowerCriterion := by
  sorry
end Thm11SourceRoute
end
