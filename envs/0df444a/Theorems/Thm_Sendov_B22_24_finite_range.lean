-- Prove2me | Theorems.Thm_Sendov_B22_24_finite_range
-- name    : Sendov.B22_24.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:28:00.342883+00:00
-- url     : https://prove2.me/theorems/fb068fb0-514e-4306-8c75-b67412058793
-- title:
--   B22 24: finite range
-- statement:
--   **The batch `22 ≤ n ≤ 24`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L146-L173
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L146-L173

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
set_option maxHeartbeats 2000000

theorem Sendov.B22_24.finite_range {n : ℕ} (h0 : 22 ≤ n) (h1 : n ≤ 24) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
