-- Prove2me | Theorems.Thm_Sendov_B24_26_finite_range
-- name    : Sendov.B24_26.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:28:40.998801+00:00
-- url     : https://prove2.me/theorems/1bac2a8c-07fe-4978-ba8f-ea31351f41d1
-- title:
--   B24 26: finite range
-- statement:
--   **The batch `24 ≤ n ≤ 26`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L150-L177
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L150-L177

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
set_option maxHeartbeats 2000000

theorem Sendov.B24_26.finite_range {n : ℕ} (h0 : 24 ≤ n) (h1 : n ≤ 26) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
