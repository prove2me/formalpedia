-- Prove2me | Theorems.Thm_Sendov_B12_13_c_lo
-- name    : Sendov.B12_13.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:49.267515+00:00
-- url     : https://prove2.me/theorems/ca112c17-d0ea-589d-a0af-cb8f6bc199eb
-- title:
--   B12 13: c lo
-- statement:
--   The B12 13 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13

theorem Sendov.B12_13.c_lo {α : ℝ} (hα : 0 ≤ α) : c 12 α = (66 + 5 * α - 2 * α ^ 2) / (22 * (3 + α)) := by sorry
