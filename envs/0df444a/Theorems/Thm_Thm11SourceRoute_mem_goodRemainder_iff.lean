-- Prove2me | Theorems.Thm_Thm11SourceRoute_mem_goodRemainder_iff
-- name    : Thm11SourceRoute.mem_goodRemainder_iff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:03:53.836714+00:00
-- url     : https://prove2.me/theorems/e5cd2c50-2373-4f2f-883d-d47668bd02b1
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000: Thm11SourceRoute.mem_goodRemainder_iff
-- statement:
--   Source theorem `Thm11SourceRoute.mem_goodRemainder_iff` extracted from `ProbabilityTheory.chapter_01.thm_1_1_bad_cells`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem mem_goodRemainder_iff {a b x : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    x ∈ goodRemainder a b S rho ↔
      x ∈ Icc a b ∧ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
  sorry
end Thm11SourceRoute
end
