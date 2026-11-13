-- Prove2me | Theorems.Thm_Thm11SourceRoute_partition_cell_endpoints_abs_lt_of_meets_half_radius
-- name    : Thm11SourceRoute.partition_cell_endpoints_abs_lt_of_meets_half_radius
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:13:24.172335+00:00
-- url     : https://prove2.me/theorems/eceb5e8f-0530-480f-985d-5ec3bf0d961a
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.partition_cell_endpoints_abs_lt_of_meets_half_radius
-- statement:
--   Source theorem `Thm11SourceRoute.partition_cell_endpoints_abs_lt_of_meets_half_radius` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem partition_cell_endpoints_abs_lt_of_meets_half_radius
    {a b c r : ℝ} (P : Partition a b) {i : Fin P.n}
    (_hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    |P.pts i.castSucc - c| < r ∧ |P.pts i.succ - c| < r := by sorry

end Thm11SourceRoute
