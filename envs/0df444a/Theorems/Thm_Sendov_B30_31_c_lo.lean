-- Prove2me | Theorems.Thm_Sendov_B30_31_c_lo
-- name    : Sendov.B30_31.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:08.497836+00:00
-- url     : https://prove2.me/theorems/e6aededd-37ff-51d2-9f06-53f72c6712a5
-- title:
--   B30 31: c lo
-- statement:
--   The B30 31 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31

theorem Sendov.B30_31.c_lo {α : ℝ} (hα : 0 ≤ α) : c 30 α = (174 + 23 * α - 2 * α ^ 2) / (58 * (3 + α)) := by sorry
