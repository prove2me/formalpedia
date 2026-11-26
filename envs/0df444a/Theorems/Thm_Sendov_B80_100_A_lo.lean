-- Prove2me | Theorems.Thm_Sendov_B80_100_A_lo
-- name    : Sendov.B80_100.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:37.241957+00:00
-- url     : https://prove2.me/theorems/99e73aa3-3ed9-4b0e-af79-0a92004788fb
-- title:
--   B80 100: A lo
-- statement:
--   The B80 100 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100

theorem Sendov.B80_100.A_lo (α : ℝ) : A 80 α = 1 - 2 * α / 79 := by sorry
