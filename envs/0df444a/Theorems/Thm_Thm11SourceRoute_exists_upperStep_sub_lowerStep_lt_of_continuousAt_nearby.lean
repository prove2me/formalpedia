-- Prove2me | Theorems.Thm_Thm11SourceRoute_exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby
-- name    : Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:26:25.590916+00:00
-- url     : https://prove2.me/theorems/d5463445-b430-46b6-827b-9f76af36cf5f
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby
-- statement:
--   Source theorem `Thm11SourceRoute.exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F002
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby
    {f : ℝ → ℝ} {a b c eps : ℝ}
    (hf : ContinuousAt f c)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : Partition a b) (i : Fin P.n),
        |P.pts i.castSucc - c| < delta →
        |P.pts i.succ - c| < delta →
          upperStep P f i - lowerStep P f i < eps := by sorry

end Thm11SourceRoute
