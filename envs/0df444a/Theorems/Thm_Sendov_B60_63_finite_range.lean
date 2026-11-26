-- Prove2me | Theorems.Thm_Sendov_B60_63_finite_range
-- name    : Sendov.B60_63.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:47:36.356907+00:00
-- url     : https://prove2.me/theorems/58104d1b-cc60-4f96-815f-4d4e8f2d92cd
-- title:
--   B60 63: finite range
-- statement:
--   **The batch `60 ≤ n ≤ 63`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L222-L249
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L222-L249

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
set_option maxHeartbeats 2000000

theorem Sendov.B60_63.finite_range {n : ℕ} (h0 : 60 ≤ n) (h1 : n ≤ 63) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
