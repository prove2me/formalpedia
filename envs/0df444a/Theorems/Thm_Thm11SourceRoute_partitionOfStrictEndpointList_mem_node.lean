-- Prove2me | Theorems.Thm_Thm11SourceRoute_partitionOfStrictEndpointList_mem_node
-- name    : Thm11SourceRoute.partitionOfStrictEndpointList_mem_node
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:00:41.43858+00:00
-- url     : https://prove2.me/theorems/5a4de334-d505-4c62-b031-c5813ba00b6e
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F001: Thm11SourceRoute.partitionOfStrictEndpointList_mem_node
-- statement:
--   Source theorem `Thm11SourceRoute.partitionOfStrictEndpointList_mem_node` extracted from `ProbabilityTheory.chapter_01.thm_1_1_common_refinement_points`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_common_refinement_points.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_refinement_points_F000
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem partitionOfStrictEndpointList_mem_node {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    {x : ℝ} (hx : x ∈ l) :
    ∃ j : Fin ((partitionOfStrictEndpointList l hlen hstart hend hstrict).n + 1),
      (partitionOfStrictEndpointList l hlen hstart hend hstrict).pts j = x := by
  sorry
end Thm11SourceRoute
end
