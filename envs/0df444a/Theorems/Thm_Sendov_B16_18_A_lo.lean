-- Prove2me | Theorems.Thm_Sendov_B16_18_A_lo
-- name    : Sendov.B16_18.A_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:24:41.253992+00:00
-- url     : https://prove2.me/theorems/8897ecd0-9232-485d-ba3b-b7930bf11bf0
-- title:
--   B16 18: A lo
-- statement:
--   The B16 18 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18

theorem Sendov.B16_18.A_lo (α : ℝ) : A 16 α = 1 - 2 * α / 15 := by sorry
