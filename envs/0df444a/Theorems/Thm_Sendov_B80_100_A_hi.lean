-- Prove2me | Theorems.Thm_Sendov_B80_100_A_hi
-- name    : Sendov.B80_100.A_hi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:33.094104+00:00
-- url     : https://prove2.me/theorems/98dce656-48d6-4a71-b14f-7b79fbb8c367
-- title:
--   B80 100: A hi
-- statement:
--   The B80 100 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100

theorem Sendov.B80_100.A_hi (α : ℝ) : A 100 α = 1 - 2 * α / 99 := by sorry
