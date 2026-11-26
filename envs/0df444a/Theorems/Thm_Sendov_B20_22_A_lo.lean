-- Prove2me | Theorems.Thm_Sendov_B20_22_A_lo
-- name    : Sendov.B20_22.A_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:26:23.987846+00:00
-- url     : https://prove2.me/theorems/4a0ff6a5-92de-40e5-ba62-1d93395fcf45
-- title:
--   B20 22: A lo
-- statement:
--   The B20 22 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22

theorem Sendov.B20_22.A_lo (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by sorry
