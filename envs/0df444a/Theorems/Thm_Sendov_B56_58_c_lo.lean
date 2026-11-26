-- Prove2me | Theorems.Thm_Sendov_B56_58_c_lo
-- name    : Sendov.B56_58.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:30:22.600804+00:00
-- url     : https://prove2.me/theorems/e09f54c7-6bf1-555f-95da-f64bd2451c0e
-- title:
--   B56 58: c lo
-- statement:
--   The B56 58 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58

theorem Sendov.B56_58.c_lo {α : ℝ} (hα : 0 ≤ α) : c 56 α = (330 + 49 * α - 2 * α ^ 2) / (110 * (3 + α)) := by sorry
