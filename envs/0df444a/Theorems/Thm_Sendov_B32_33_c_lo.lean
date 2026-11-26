-- Prove2me | Theorems.Thm_Sendov_B32_33_c_lo
-- name    : Sendov.B32_33.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:13:51.274242+00:00
-- url     : https://prove2.me/theorems/5fba7c2d-069f-52ae-a018-3bf1d5b6409d
-- title:
--   B32 33: c lo
-- statement:
--   The B32 33 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33

theorem Sendov.B32_33.c_lo {α : ℝ} (hα : 0 ≤ α) : c 32 α = (186 + 25 * α - 2 * α ^ 2) / (62 * (3 + α)) := by sorry
