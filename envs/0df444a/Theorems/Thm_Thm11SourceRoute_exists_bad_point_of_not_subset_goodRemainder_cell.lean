-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_bad_point_of_not_subset_goodRemainder_cell
-- name    : Thm11SourceRoute.exists_bad_point_of_not_subset_goodRemainder_cell
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:05:10.167122+00:00
-- url     : https://prove2.me/theorems/09ee9f71-01f2-4cf0-a117-ae2ea966a451
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.exists_bad_point_of_not_subset_goodRemainder_cell
-- statement:
--   Source theorem `Thm11SourceRoute.exists_bad_point_of_not_subset_goodRemainder_cell` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem exists_bad_point_of_not_subset_goodRemainder_cell
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆ goodRemainder a b S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c := by sorry

end Thm11SourceRoute
