-- Prove2me | Theorems.Thm_Thm11SourceRoute_partition_cell_increment_le_bad_interval
-- name    : Thm11SourceRoute.partition_cell_increment_le_bad_interval
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:09:14.553818+00:00
-- url     : https://prove2.me/theorems/51df5892-2008-4bcf-8d3f-11ebfcbd7e75
-- title:
--   Source theorem: Thm11SourceRoute.partition_cell_increment_le_bad_interval
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_01.thm_1_1_bad_cells, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem partition_cell_increment_le_bad_interval
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {i : Fin P.n}
    (hleft : |P.pts i.castSucc - c| < r)
    (hright : |P.pts i.succ - c| < r) :
    α (P.pts i.succ) - α (P.pts i.castSucc) ≤ α (c + r) - α (c - r) := by
  sorry
end Thm11SourceRoute
end
