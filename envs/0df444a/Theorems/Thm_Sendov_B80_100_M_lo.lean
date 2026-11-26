-- Prove2me | Theorems.Thm_Sendov_B80_100_M_lo
-- name    : Sendov.B80_100.M_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:22.284079+00:00
-- url     : https://prove2.me/theorems/ea5a265c-d2fe-53c6-8cd9-b95ddf357f0e
-- title:
--   B80 100: M lo
-- statement:
--   The B80 100 construction uses the M lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L30-L30
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L30-L30

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100

theorem Sendov.B80_100.M_lo : M 80 = 79 := by sorry
