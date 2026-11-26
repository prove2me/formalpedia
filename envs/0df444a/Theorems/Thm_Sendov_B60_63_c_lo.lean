-- Prove2me | Theorems.Thm_Sendov_B60_63_c_lo
-- name    : Sendov.B60_63.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:35:30.078528+00:00
-- url     : https://prove2.me/theorems/f3dab66b-501a-5d1d-913b-871c831471fa
-- title:
--   B60 63: c lo
-- statement:
--   The B60 63 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63

theorem Sendov.B60_63.c_lo {α : ℝ} (hα : 0 ≤ α) : c 60 α = (354 + 53 * α - 2 * α ^ 2) / (118 * (3 + α)) := by sorry
