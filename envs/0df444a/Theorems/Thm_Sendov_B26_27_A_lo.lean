-- Prove2me | Theorems.Thm_Sendov_B26_27_A_lo
-- name    : Sendov.B26_27.A_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:28:57.120343+00:00
-- url     : https://prove2.me/theorems/699136c3-b97a-5b8a-80da-1c631ea74ec4
-- title:
--   B26 27: A lo
-- statement:
--   The B26 27 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27

theorem Sendov.B26_27.A_lo (α : ℝ) : A 26 α = 1 - 2 * α / 25 := by sorry
