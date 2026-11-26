-- Prove2me | Theorems.Thm_Sendov_B58_60_c_lo
-- name    : Sendov.B58_60.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:32:27.864794+00:00
-- url     : https://prove2.me/theorems/42e92058-481a-46b9-bd73-05fc1d2bad1c
-- title:
--   B58 60: c lo
-- statement:
--   The B58 60 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60

theorem Sendov.B58_60.c_lo {α : ℝ} (hα : 0 ≤ α) : c 58 α = (342 + 51 * α - 2 * α ^ 2) / (114 * (3 + α)) := by sorry
