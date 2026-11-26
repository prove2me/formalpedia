-- Prove2me | Theorems.Thm_Sendov_B12_13_A_hi
-- name    : Sendov.B12_13.A_hi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:45.01145+00:00
-- url     : https://prove2.me/theorems/200b429a-df56-550b-aea0-0e3341b8fd7e
-- title:
--   B12 13: A hi
-- statement:
--   The B12 13 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13

theorem Sendov.B12_13.A_hi (α : ℝ) : A 13 α = 1 - 2 * α / 12 := by sorry
