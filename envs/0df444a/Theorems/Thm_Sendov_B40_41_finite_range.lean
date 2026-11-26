-- Prove2me | Theorems.Thm_Sendov_B40_41_finite_range
-- name    : Sendov.B40_41.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:36:34.156316+00:00
-- url     : https://prove2.me/theorems/82cdd2a2-1325-4af0-8238-5bc22093e19c
-- title:
--   B40 41: finite range
-- statement:
--   **The batch `40 ≤ n ≤ 41`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L182-L209
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L182-L209

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
set_option maxHeartbeats 2000000

theorem Sendov.B40_41.finite_range {n : ℕ} (h0 : 40 ≤ n) (h1 : n ≤ 41) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
