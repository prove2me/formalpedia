-- Prove2me | Theorems.Thm_Sendov_B34_35_c_lo
-- name    : Sendov.B34_35.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:14:26.013787+00:00
-- url     : https://prove2.me/theorems/452562e9-68fc-57f8-abf4-cdb17c56ffe5
-- title:
--   B34 35: c lo
-- statement:
--   The B34 35 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35

theorem Sendov.B34_35.c_lo {α : ℝ} (hα : 0 ≤ α) : c 34 α = (198 + 27 * α - 2 * α ^ 2) / (66 * (3 + α)) := by sorry
