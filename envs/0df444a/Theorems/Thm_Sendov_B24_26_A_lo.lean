-- Prove2me | Theorems.Thm_Sendov_B24_26_A_lo
-- name    : Sendov.B24_26.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:28:19.160958+00:00
-- url     : https://prove2.me/theorems/f2cfc378-12f6-45c8-a99d-1377f53d5373
-- title:
--   B24 26: A lo
-- statement:
--   The B24 26 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26

theorem Sendov.B24_26.A_lo (α : ℝ) : A 24 α = 1 - 2 * α / 23 := by sorry
