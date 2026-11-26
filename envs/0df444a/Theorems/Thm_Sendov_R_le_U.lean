-- Prove2me | Theorems.Thm_Sendov_R_le_U
-- name    : Sendov.R_le_U
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:48:29.861644+00:00
-- url     : https://prove2.me/theorems/7147681c-3268-4608-9b47-79880356d13f
-- title:
--   Sendov: R le U
-- statement:
--   **`R` is bounded by the elementary expression `U`.**  This is the bridge out of
--   integration: from here the large-degree argument is elementary.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L88-L92
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L88-L92

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}

theorem Sendov.R_le_U (hn : 5 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α) (hc : 0 < c n α) :
    R n α ≤ U n α := by sorry
