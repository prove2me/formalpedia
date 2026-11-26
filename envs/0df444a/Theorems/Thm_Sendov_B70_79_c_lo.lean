-- Prove2me | Theorems.Thm_Sendov_B70_79_c_lo
-- name    : Sendov.B70_79.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:42:03.968793+00:00
-- url     : https://prove2.me/theorems/9bab15e1-1a83-56f6-bb92-402ff502c9b9
-- title:
--   B70 79: c lo
-- statement:
--   The B70 79 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree70_79.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree70_79.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79

theorem Sendov.B70_79.c_lo {α : ℝ} (hα : 0 ≤ α) : c 70 α = (414 + 63 * α - 2 * α ^ 2) / (138 * (3 + α)) := by sorry
