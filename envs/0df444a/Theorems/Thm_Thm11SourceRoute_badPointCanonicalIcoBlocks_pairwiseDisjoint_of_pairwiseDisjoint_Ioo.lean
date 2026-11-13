-- Prove2me | Theorems.Thm_Thm11SourceRoute_badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
-- name    : Thm11SourceRoute.badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:44:51.613708+00:00
-- url     : https://prove2.me/theorems/dde9d276-d4be-4d41-a1c1-1ab024f16ad1
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
-- statement:
--   Source theorem `Thm11SourceRoute.badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F006
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
    {a b : ℝ} (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ =>
        Finset.Ico (badPointCanonicalLo P c (rho c))
          (badPointCanonicalHi P c (rho c))) := by sorry

end Thm11SourceRoute
