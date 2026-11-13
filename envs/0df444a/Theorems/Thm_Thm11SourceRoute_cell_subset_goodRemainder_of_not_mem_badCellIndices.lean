-- Prove2me | Theorems.Thm_Thm11SourceRoute_cell_subset_goodRemainder_of_not_mem_badCellIndices
-- name    : Thm11SourceRoute.cell_subset_goodRemainder_of_not_mem_badCellIndices
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:57:41.047531+00:00
-- url     : https://prove2.me/theorems/b30adb6d-73c5-4393-9d2b-cc9d9ac511c1
-- title:
--   Source theorem: Thm11SourceRoute.cell_subset_goodRemainder_of_not_mem_badCellIndices
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_01.thm_1_1_bad_cells, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem cell_subset_goodRemainder_of_not_mem_badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (i : Fin P.n)
    (hi_not_bad : i.val ∉ badCellIndices P S rho) :
    Partition.subinterval P i ⊆ goodRemainder a b S rho := by
  sorry
end Thm11SourceRoute
end
