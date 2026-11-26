-- Prove2me | Theorems.Thm_Sendov_B22_24_c_lo
-- name    : Sendov.B22_24.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:22.23262+00:00
-- url     : https://prove2.me/theorems/1df83482-e9a3-5423-8662-30e7ef84ec10
-- title:
--   B22 24: c lo
-- statement:
--   The B22 24 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24

theorem Sendov.B22_24.c_lo {α : ℝ} (hα : 0 ≤ α) : c 22 α = (126 + 15 * α - 2 * α ^ 2) / (42 * (3 + α)) := by sorry
