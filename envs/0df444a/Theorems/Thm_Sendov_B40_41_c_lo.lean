-- Prove2me | Theorems.Thm_Sendov_B40_41_c_lo
-- name    : Sendov.B40_41.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:17:56.901806+00:00
-- url     : https://prove2.me/theorems/d9b2c82a-357a-5e2b-8640-d8e44d131c33
-- title:
--   B40 41: c lo
-- statement:
--   The B40 41 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41

theorem Sendov.B40_41.c_lo {α : ℝ} (hα : 0 ≤ α) : c 40 α = (234 + 33 * α - 2 * α ^ 2) / (78 * (3 + α)) := by sorry
