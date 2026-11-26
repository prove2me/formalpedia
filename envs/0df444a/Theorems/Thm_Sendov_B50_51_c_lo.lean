-- Prove2me | Theorems.Thm_Sendov_B50_51_c_lo
-- name    : Sendov.B50_51.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:24:12.021889+00:00
-- url     : https://prove2.me/theorems/e120f198-ea8a-4291-a321-a9e17f1aee9e
-- title:
--   B50 51: c lo
-- statement:
--   The B50 51 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51

theorem Sendov.B50_51.c_lo {α : ℝ} (hα : 0 ≤ α) : c 50 α = (294 + 43 * α - 2 * α ^ 2) / (98 * (3 + α)) := by sorry
