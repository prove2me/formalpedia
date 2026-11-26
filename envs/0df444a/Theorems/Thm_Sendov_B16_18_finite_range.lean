-- Prove2me | Theorems.Thm_Sendov_B16_18_finite_range
-- name    : Sendov.B16_18.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:25:11.288613+00:00
-- url     : https://prove2.me/theorems/81852023-1806-49da-8ac5-010ab7572280
-- title:
--   B16 18: finite range
-- statement:
--   **The batch `16 ≤ n ≤ 18`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L134-L161
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L134-L161

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
set_option maxHeartbeats 2000000

theorem Sendov.B16_18.finite_range {n : ℕ} (h0 : 16 ≤ n) (h1 : n ≤ 18) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
