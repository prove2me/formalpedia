-- Prove2me | Theorems.Thm_Sendov_B16_18_c_lo
-- name    : Sendov.B16_18.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:30.390014+00:00
-- url     : https://prove2.me/theorems/2a7b7d20-4a44-587e-abdf-9cdd5cc44d40
-- title:
--   B16 18: c lo
-- statement:
--   The B16 18 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18

theorem Sendov.B16_18.c_lo {α : ℝ} (hα : 0 ≤ α) : c 16 α = (90 + 9 * α - 2 * α ^ 2) / (30 * (3 + α)) := by sorry
