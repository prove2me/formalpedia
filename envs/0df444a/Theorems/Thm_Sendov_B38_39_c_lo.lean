-- Prove2me | Theorems.Thm_Sendov_B38_39_c_lo
-- name    : Sendov.B38_39.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:16:28.330997+00:00
-- url     : https://prove2.me/theorems/c9005c1b-f414-40a3-9c83-49d87be2becc
-- title:
--   B38 39: c lo
-- statement:
--   The B38 39 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39

theorem Sendov.B38_39.c_lo {α : ℝ} (hα : 0 ≤ α) : c 38 α = (222 + 31 * α - 2 * α ^ 2) / (74 * (3 + α)) := by sorry
