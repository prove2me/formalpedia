-- Prove2me | Theorems.Thm_Sendov_B22_24_A_lo
-- name    : Sendov.B22_24.A_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:27:16.6378+00:00
-- url     : https://prove2.me/theorems/0b8cd37e-3559-4eb1-8410-5920b98a5b84
-- title:
--   B22 24: A lo
-- statement:
--   The B22 24 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24

theorem Sendov.B22_24.A_lo (α : ℝ) : A 22 α = 1 - 2 * α / 21 := by sorry
