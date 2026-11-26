-- Prove2me | Theorems.Thm_Sendov_B44_45_c_lo
-- name    : Sendov.B44_45.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:20:01.05699+00:00
-- url     : https://prove2.me/theorems/1902d8c6-d9f5-510b-a919-aa4c8aaf3c63
-- title:
--   B44 45: c lo
-- statement:
--   The B44 45 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree44_45.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree44_45.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree44_45
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B44_45

theorem Sendov.B44_45.c_lo {α : ℝ} (hα : 0 ≤ α) : c 44 α = (258 + 37 * α - 2 * α ^ 2) / (86 * (3 + α)) := by sorry
