-- Prove2me | Theorems.Thm_Sendov_B26_27_c_lo
-- name    : Sendov.B26_27.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:10:55.876117+00:00
-- url     : https://prove2.me/theorems/b93ad873-5790-445a-9e75-d16307a7db4a
-- title:
--   B26 27: c lo
-- statement:
--   The B26 27 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27

theorem Sendov.B26_27.c_lo {α : ℝ} (hα : 0 ≤ α) : c 26 α = (150 + 19 * α - 2 * α ^ 2) / (50 * (3 + α)) := by sorry
