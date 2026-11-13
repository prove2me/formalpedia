-- Prove2me | Theorems.Thm_Thm11SourceRoute_isCompact_goodRemainder
-- name    : Thm11SourceRoute.isCompact_goodRemainder
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:04:07.691265+00:00
-- url     : https://prove2.me/theorems/ae9d9e5e-df17-4d2d-9f5d-1b14b734f1f5
-- title:
--   ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000: Thm11SourceRoute.isCompact_goodRemainder
-- statement:
--   Source theorem `Thm11SourceRoute.isCompact_goodRemainder` extracted from `ProbabilityTheory.chapter_01.thm_1_1_bad_cells`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
open Finset BigOperators
open Set Topology
noncomputable section
namespace Thm11SourceRoute

theorem isCompact_goodRemainder {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    IsCompact (goodRemainder a b S rho) := by
  sorry
end Thm11SourceRoute
end
