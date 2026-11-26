-- Prove2me | Theorems.Thm_Sendov_B28_29_c_lo
-- name    : Sendov.B28_29.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:44.612474+00:00
-- url     : https://prove2.me/theorems/473afa3e-4a61-432a-8053-534960846fa6
-- title:
--   B28 29: c lo
-- statement:
--   The B28 29 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29

theorem Sendov.B28_29.c_lo {α : ℝ} (hα : 0 ≤ α) : c 28 α = (162 + 21 * α - 2 * α ^ 2) / (54 * (3 + α)) := by sorry
