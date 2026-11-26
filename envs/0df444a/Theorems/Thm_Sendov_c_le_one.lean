-- Prove2me | Theorems.Thm_Sendov_c_le_one
-- name    : Sendov.c_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:00.014558+00:00
-- url     : https://prove2.me/theorems/bcd2a8f0-f09a-544e-b816-67f3ee14ecb6
-- title:
--   Sendov: c le one
-- statement:
--   `c ≤ 1`, so the chord's zero `1/c` is at least `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L36-L42
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L36-L42

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}

theorem Sendov.c_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) : c n α ≤ 1 := by sorry
