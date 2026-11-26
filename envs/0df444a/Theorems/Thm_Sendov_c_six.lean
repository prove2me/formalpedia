-- Prove2me | Theorems.Thm_Sendov_c_six
-- name    : Sendov.c_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:05.043105+00:00
-- url     : https://prove2.me/theorems/3b07a1b1-2325-5cac-b37d-73ae0759bdf5
-- title:
--   Sendov: c six
-- statement:
--   The Sendov construction uses the c six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L39-L39
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L39-L39

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.c_six (α : ℝ) : c 6 α = 1 - α / 5 - α / (2 * (3 + α)) := by sorry
