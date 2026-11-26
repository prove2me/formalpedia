-- Prove2me | Theorems.Thm_Sendov_rpow_add_half_le
-- name    : Sendov.rpow_add_half_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:15.351049+00:00
-- url     : https://prove2.me/theorems/d0527105-0a7c-51c0-9bab-17ad626d0486
-- title:
--   Sendov: rpow add half le
-- statement:
--   The half-integer power bound `q ^ (k + 1/2) ≤ q ^ k * (q/(2w) + w/2)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/OddBound.lean#L45-L55
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/OddBound.lean#L45-L55

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_OddBound
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}

theorem Sendov.rpow_add_half_le (hq : 0 ≤ q) (k : ℕ) (hw : 0 < w) :
    q ^ ((k : ℝ) + 1 / 2) ≤ q ^ k * (q / (2 * w) + w / 2) := by sorry
