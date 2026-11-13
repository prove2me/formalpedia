-- Prove2me | Theorems.Thm_Thm11SourceRoute_commonRefinementPointList_adjacent_length_lt_delta
-- name    : Thm11SourceRoute.commonRefinementPointList_adjacent_length_lt_delta
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:59:57.475209+00:00
-- url     : https://prove2.me/theorems/961ee0d2-d0ed-4492-8d11-b79087123324
-- title:
--   Chapter 1, thm_1_1_common_refinement_points: Thm11SourceRoute.commonRefinementPointList_adjacent_length_lt_delta
-- statement:
--   Source theorem `Thm11SourceRoute.commonRefinementPointList_adjacent_length_lt_delta` from Chapter 1, module `thm_1_1_common_refinement_points`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_refinement_points.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem commonRefinementPointList_adjacent_length_lt_delta {a b δ : ℝ}
    (P Q : Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ)
    {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b < δ := by sorry

end Thm11SourceRoute
