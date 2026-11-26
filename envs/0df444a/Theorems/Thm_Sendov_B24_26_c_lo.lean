-- Prove2me | Theorems.Thm_Sendov_B24_26_c_lo
-- name    : Sendov.B24_26.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:48.950577+00:00
-- url     : https://prove2.me/theorems/aee4a37e-6fde-4622-a7a8-89a160217415
-- title:
--   B24 26: c lo
-- statement:
--   The B24 26 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26

theorem Sendov.B24_26.c_lo {α : ℝ} (hα : 0 ≤ α) : c 24 α = (138 + 17 * α - 2 * α ^ 2) / (46 * (3 + α)) := by sorry
