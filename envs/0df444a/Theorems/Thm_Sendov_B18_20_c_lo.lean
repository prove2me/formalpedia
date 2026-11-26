-- Prove2me | Theorems.Thm_Sendov_B18_20_c_lo
-- name    : Sendov.B18_20.c_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:48.735896+00:00
-- url     : https://prove2.me/theorems/33afaeb4-1cbd-58a6-99d6-55aaac8dfa96
-- title:
--   B18 20: c lo
-- statement:
--   The B18 20 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20

theorem Sendov.B18_20.c_lo {α : ℝ} (hα : 0 ≤ α) : c 18 α = (102 + 11 * α - 2 * α ^ 2) / (34 * (3 + α)) := by sorry
