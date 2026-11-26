-- Prove2me | Theorems.Thm_Sendov_B52_53_A_lo
-- name    : Sendov.B52_53.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:41:12.522309+00:00
-- url     : https://prove2.me/theorems/c3e92723-c691-5342-b983-24c250b407a5
-- title:
--   B52 53: A lo
-- statement:
--   The B52 53 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree52_53.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree52_53.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53

theorem Sendov.B52_53.A_lo (α : ℝ) : A 52 α = 1 - 2 * α / 51 := by sorry
