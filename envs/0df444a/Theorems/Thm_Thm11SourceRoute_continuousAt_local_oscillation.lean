-- Prove2me | Theorems.Thm_Thm11SourceRoute_continuousAt_local_oscillation
-- name    : Thm11SourceRoute.continuousAt_local_oscillation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:25:46.139205+00:00
-- url     : https://prove2.me/theorems/514da935-41c3-499c-ab36-a00d8489fa64
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: Thm11SourceRoute.continuousAt_local_oscillation
-- statement:
--   Source theorem `Thm11SourceRoute.continuousAt_local_oscillation` from Chapter 1, module `thm_1_1_oscillation_basic`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F001
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem continuousAt_local_oscillation {f : ℝ → ℝ} {c eps : ℝ}
    (hf : ContinuousAt f c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x y : ℝ,
        |x - c| < delta → |y - c| < delta → |f x - f y| < eps := by sorry

end Thm11SourceRoute
