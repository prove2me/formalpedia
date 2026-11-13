-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_bad_point_of_mem_badCellIndices
-- name    : Thm11SourceRoute.exists_bad_point_of_mem_badCellIndices
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:08:59.616229+00:00
-- url     : https://prove2.me/theorems/46679c47-d50f-452e-aedf-c30db40e4429
-- title:
--   Source theorem: Thm11SourceRoute.exists_bad_point_of_mem_badCellIndices
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

theorem exists_bad_point_of_mem_badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    {i : ℕ} (hi_bad : i ∈ badCellIndices P S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      ∃ hi : i < P.n, x ∈ Partition.subinterval P ⟨i, hi⟩ ∧ |x - c| < rho c := by
  sorry
end Thm11SourceRoute
end
