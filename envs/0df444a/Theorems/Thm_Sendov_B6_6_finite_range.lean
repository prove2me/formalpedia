-- Prove2me | Theorems.Thm_Sendov_B6_6_finite_range
-- name    : Sendov.B6_6.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:20:43.251847+00:00
-- url     : https://prove2.me/theorems/ac494cf7-103c-5a24-be35-10dacf57e8d8
-- title:
--   B6 6: finite range
-- statement:
--   **The batch `6 ≤ n ≤ 6`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L114-L141
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L114-L141

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
set_option maxHeartbeats 2000000

theorem Sendov.B6_6.finite_range {n : ℕ} (h0 : 6 ≤ n) (h1 : n ≤ 6) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
