-- Prove2me | Theorems.Thm_Sendov_B80_100_c_lo
-- name    : Sendov.B80_100.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:33.8959+00:00
-- url     : https://prove2.me/theorems/fbfbb15c-6225-4ad3-a8f0-a08972e7a168
-- title:
--   B80 100: c lo
-- statement:
--   The B80 100 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100

theorem Sendov.B80_100.c_lo {α : ℝ} (hα : 0 ≤ α) : c 80 α = (474 + 73 * α - 2 * α ^ 2) / (158 * (3 + α)) := by sorry
