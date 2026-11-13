-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
-- name    : Thm11SourceRoute.exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:13:13.663193+00:00
-- url     : https://prove2.me/theorems/6e8a87a5-af70-4686-97ef-abbd79c5390e
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F004: Thm11SourceRoute.exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
-- statement:
--   Source theorem `Thm11SourceRoute.exists_bad_point_half_radius_of_not_subset_goodRemainder_cell` from `ProbabilityTheory.chapter_01.thm_1_1_bad_cells`. The formal Lean declaration specifies its proposition.
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

theorem exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆
        goodRemainder a b S (fun c : ℝ => rho c / 2)) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c / 2 := by
  sorry
end Thm11SourceRoute
end
