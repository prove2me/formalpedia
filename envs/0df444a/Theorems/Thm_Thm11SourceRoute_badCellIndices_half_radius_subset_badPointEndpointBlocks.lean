-- Prove2me | Theorems.Thm_Thm11SourceRoute_badCellIndices_half_radius_subset_badPointEndpointBlocks
-- name    : Thm11SourceRoute.badCellIndices_half_radius_subset_badPointEndpointBlocks
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:14:13.086221+00:00
-- url     : https://prove2.me/theorems/6e2b97fe-6505-44ca-9148-d17f2cc2cfcb
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.badCellIndices_half_radius_subset_badPointEndpointBlocks
-- statement:
--   Source theorem `Thm11SourceRoute.badCellIndices_half_radius_subset_badPointEndpointBlocks` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F008
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem badCellIndices_half_radius_subset_badPointEndpointBlocks {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by sorry

end Thm11SourceRoute
