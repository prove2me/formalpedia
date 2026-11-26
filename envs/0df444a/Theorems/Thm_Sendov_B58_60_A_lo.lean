-- Prove2me | Theorems.Thm_Sendov_B58_60_A_lo
-- name    : Sendov.B58_60.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:45:48.122806+00:00
-- url     : https://prove2.me/theorems/366369bf-a63a-410e-98f9-5abd88ed11bc
-- title:
--   B58 60: A lo
-- statement:
--   The B58 60 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60

theorem Sendov.B58_60.A_lo (α : ℝ) : A 58 α = 1 - 2 * α / 57 := by sorry
