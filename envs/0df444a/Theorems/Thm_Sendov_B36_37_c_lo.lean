-- Prove2me | Theorems.Thm_Sendov_B36_37_c_lo
-- name    : Sendov.B36_37.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:14:59.042905+00:00
-- url     : https://prove2.me/theorems/990af0f9-34dc-50b7-9fc4-7f4d7f0b1ede
-- title:
--   B36 37: c lo
-- statement:
--   The B36 37 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37

theorem Sendov.B36_37.c_lo {α : ℝ} (hα : 0 ≤ α) : c 36 α = (210 + 29 * α - 2 * α ^ 2) / (70 * (3 + α)) := by sorry
