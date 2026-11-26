-- Prove2me | Theorems.Thm_Sendov_B80_100_finite_range
-- name    : Sendov.B80_100.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:34.148285+00:00
-- url     : https://prove2.me/theorems/990b67d8-6ca0-5e39-89af-aff1e187612b
-- title:
--   B80 100: finite range
-- statement:
--   **The batch `80 ≤ n ≤ 100`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L164-L191
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L164-L191

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100
set_option maxHeartbeats 2000000

theorem Sendov.B80_100.finite_range {n : ℕ} (h0 : 80 ≤ n) (h1 : n ≤ 100) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
