-- Prove2me | Theorems.Thm_Sendov_B20_22_c_lo
-- name    : Sendov.B20_22.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:51.523854+00:00
-- url     : https://prove2.me/theorems/94f105db-4d42-586e-b71a-ba1970bf10a3
-- title:
--   B20 22: c lo
-- statement:
--   The B20 22 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22

theorem Sendov.B20_22.c_lo {α : ℝ} (hα : 0 ≤ α) : c 20 α = (114 + 13 * α - 2 * α ^ 2) / (38 * (3 + α)) := by sorry
