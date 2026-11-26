-- Prove2me | Theorems.Thm_Sendov_B14_15_A_lo
-- name    : Sendov.B14_15.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:23:20.76799+00:00
-- url     : https://prove2.me/theorems/e5199e1b-5004-55c0-8fd8-33dbb66139fe
-- title:
--   B14 15: A lo
-- statement:
--   The B14 15 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15

theorem Sendov.B14_15.A_lo (α : ℝ) : A 14 α = 1 - 2 * α / 13 := by sorry
