-- Prove2me | Theorems.Thm_Sendov_B18_20_A_lo
-- name    : Sendov.B18_20.A_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:25:24.962801+00:00
-- url     : https://prove2.me/theorems/04253613-efb7-46b3-9f34-243d26c76f71
-- title:
--   B18 20: A lo
-- statement:
--   The B18 20 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20

theorem Sendov.B18_20.A_lo (α : ℝ) : A 18 α = 1 - 2 * α / 17 := by sorry
