-- Prove2me | Theorems.Thm_Sendov_B12_13_A_lo
-- name    : Sendov.B12_13.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:22:35.820194+00:00
-- url     : https://prove2.me/theorems/a2561b6b-17e7-45bf-aee8-c223b72845e7
-- title:
--   B12 13: A lo
-- statement:
--   The B12 13 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13

theorem Sendov.B12_13.A_lo (α : ℝ) : A 12 α = 1 - 2 * α / 11 := by sorry
