-- Prove2me | Theorems.Thm_Sendov_B28_29_finite_range
-- name    : Sendov.B28_29.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:30:39.62645+00:00
-- url     : https://prove2.me/theorems/cb09eaa3-02b2-4b9d-ae2b-bd1a480ed08f
-- title:
--   B28 29: finite range
-- statement:
--   **The batch `28 ≤ n ≤ 29`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L158-L185
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L158-L185

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
set_option maxHeartbeats 2000000

theorem Sendov.B28_29.finite_range {n : ℕ} (h0 : 28 ≤ n) (h1 : n ≤ 29) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
