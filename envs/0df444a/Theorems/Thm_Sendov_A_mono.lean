-- Prove2me | Theorems.Thm_Sendov_A_mono
-- name    : Sendov.A_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:48.706893+00:00
-- url     : https://prove2.me/theorems/d4ea9b6f-a605-5eae-8bd6-a22781082973
-- title:
--   Sendov: A mono
-- statement:
--   `A` increases with `n`: raising the degree moves `a²` towards `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L49-L55
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L49-L55

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
set_option autoImplicit false
open Sendov
variable {α t : ℝ}

theorem Sendov.A_mono {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : A m α ≤ A n α := by sorry
