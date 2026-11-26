-- Prove2me | Theorems.Thm_Sendov_B52_53_finite_range
-- name    : Sendov.B52_53.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:42:40.415752+00:00
-- url     : https://prove2.me/theorems/4d4adcb4-d115-42a7-8788-66edb8d99c73
-- title:
--   B52 53: finite range
-- statement:
--   **The batch `52 ≤ n ≤ 53`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree52_53.lean#L206-L233
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree52_53.lean#L206-L233

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53
set_option maxHeartbeats 2000000

theorem Sendov.B52_53.finite_range {n : ℕ} (h0 : 52 ≤ n) (h1 : n ≤ 53) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
