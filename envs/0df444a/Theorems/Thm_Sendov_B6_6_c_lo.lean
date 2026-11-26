-- Prove2me | Theorems.Thm_Sendov_B6_6_c_lo
-- name    : Sendov.B6_6.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:05:49.554423+00:00
-- url     : https://prove2.me/theorems/7752e18f-561e-5168-9ebd-810c4975acf5
-- title:
--   B6 6: c lo
-- statement:
--   The B6 6 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6

theorem Sendov.B6_6.c_lo {α : ℝ} (hα : 0 ≤ α) : c 6 α = (30 - 1 * α - 2 * α ^ 2) / (10 * (3 + α)) := by sorry
