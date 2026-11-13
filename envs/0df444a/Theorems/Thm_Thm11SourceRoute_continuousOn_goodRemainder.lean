-- Prove2me | Theorems.Thm_Thm11SourceRoute_continuousOn_goodRemainder
-- name    : Thm11SourceRoute.continuousOn_goodRemainder
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:04:22.843776+00:00
-- url     : https://prove2.me/theorems/fd14b565-2dfa-4e5c-91ce-033ff26eba71
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.continuousOn_goodRemainder
-- statement:
--   Source theorem `Thm11SourceRoute.continuousOn_goodRemainder` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem continuousOn_goodRemainder
    {f : ℝ → ℝ} {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c) :
    ContinuousOn f (goodRemainder a b S rho) := by sorry

end Thm11SourceRoute
