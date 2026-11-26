-- Prove2me | Theorems.Thm_Sendov_B48_49_finite_range
-- name    : Sendov.B48_49.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:39:55.273961+00:00
-- url     : https://prove2.me/theorems/ca257348-0eb0-4a30-8cae-3e56a6720044
-- title:
--   B48 49: finite range
-- statement:
--   **The batch `48 ≤ n ≤ 49`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree48_49.lean#L198-L225
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree48_49.lean#L198-L225

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49
set_option maxHeartbeats 2000000

theorem Sendov.B48_49.finite_range {n : ℕ} (h0 : 48 ≤ n) (h1 : n ≤ 49) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
