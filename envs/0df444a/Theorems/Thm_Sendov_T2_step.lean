-- Prove2me | Theorems.Thm_Sendov_T2_step
-- name    : Sendov.T2_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:16.364476+00:00
-- url     : https://prove2.me/theorems/93934fcf-fd5f-5226-9a34-a11d46a9f18d
-- title:
--   Sendov: T2 step
-- statement:
--   One step of the geometric decay: `T2` decreases with `n` on `n ≥ 101`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L248-L300
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L248-L300

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.T2_step (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 (n + 1) α ≤ T2 n α := by sorry
