-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
-- name    : Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:04:52.359298+00:00
-- url     : https://prove2.me/theorems/9c470454-3283-46d2-8b68-cebfdf71b87a
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
-- statement:
--   Source theorem `Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
    {f : ℝ → ℝ} {a b eta : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : Partition a b) (i : Fin P.n),
        P.mesh < delta →
        Partition.subinterval P i ⊆ goodRemainder a b S rho →
          upperStep P f i - lowerStep P f i < eta := by sorry

end Thm11SourceRoute
