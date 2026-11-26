-- Prove2me | Theorems.Thm_Sendov_B14_15_c_lo
-- name    : Sendov.B14_15.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:09.080201+00:00
-- url     : https://prove2.me/theorems/23d1b4bb-58b2-497d-a53d-a39bb676f45b
-- title:
--   B14 15: c lo
-- statement:
--   The B14 15 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15

theorem Sendov.B14_15.c_lo {α : ℝ} (hα : 0 ≤ α) : c 14 α = (78 + 7 * α - 2 * α ^ 2) / (26 * (3 + α)) := by sorry
