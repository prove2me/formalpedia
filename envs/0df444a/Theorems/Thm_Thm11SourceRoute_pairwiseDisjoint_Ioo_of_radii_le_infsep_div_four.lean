-- Prove2me | Theorems.Thm_Thm11SourceRoute_pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four
-- name    : Thm11SourceRoute.pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:27:11.420207+00:00
-- url     : https://prove2.me/theorems/721f891f-c36b-43b8-874f-33f46607f2bb
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four
-- statement:
--   Source theorem `Thm11SourceRoute.pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F003
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_le :
      ∀ c : ℝ, c ∈ S →
        (S : Set ℝ).Nontrivial →
        rho c ≤ (S : Set ℝ).infsep / 4) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by sorry

end Thm11SourceRoute
