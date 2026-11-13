-- Prove2me | Theorems.Thm_Thm11SourceRoute_mem_badCellIndices_iff
-- name    : Thm11SourceRoute.mem_badCellIndices_iff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:57:27.759242+00:00
-- url     : https://prove2.me/theorems/9cc9baa6-d468-4f57-bc63-44b85117c3ee
-- title:
--   Source theorem: Thm11SourceRoute.mem_badCellIndices_iff
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

theorem mem_badCellIndices_iff {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) {i : ℕ} :
    i ∈ badCellIndices P S rho ↔
      i < P.n ∧
        ∀ hi : i < P.n,
          ¬ Partition.subinterval P ⟨i, hi⟩ ⊆ goodRemainder a b S rho := by
  sorry
end Thm11SourceRoute
end
