-- Prove2me | Theorems.Thm_Sendov_B46_47_c_lo
-- name    : Sendov.B46_47.c_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:21:05.319488+00:00
-- url     : https://prove2.me/theorems/7fcd997f-2e9a-4e77-8f96-5a9cd6cd9437
-- title:
--   B46 47: c lo
-- statement:
--   The B46 47 construction uses the c lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L38-L43
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L38-L43

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47

theorem Sendov.B46_47.c_lo {α : ℝ} (hα : 0 ≤ α) : c 46 α = (270 + 39 * α - 2 * α ^ 2) / (90 * (3 + α)) := by sorry
