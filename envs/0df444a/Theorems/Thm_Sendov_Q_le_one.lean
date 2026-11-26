-- Prove2me | Theorems.Thm_Sendov_Q_le_one
-- name    : Sendov.Q_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:45.574939+00:00
-- url     : https://prove2.me/theorems/68305468-f6fe-4c30-aeaf-25f38a4cee75
-- title:
--   Sendov: Q le one
-- statement:
--   `Q` is convex with `Q 0 = 1` and `Q 1 = B ≤ 1`, hence bounded by `1` on `[0,1]`.
--
--   Only `0 ≤ c` is needed, not `0 ≤ A`: writing `Q t - 1 = t (A t - 2c)`, the identity
--   `Q 1 = B < 1` gives `A ≤ 2c` outright, and then `A t ≤ 2c` holds whether `A` is nonnegative
--   (as `A t ≤ A`) or negative (as `A t ≤ 0 ≤ 2c`).  That matters for batches of degrees whose
--   `α`-range reaches past `(n₀-1)/2`, where `A n₀ α` can be negative.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L85-L98
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L85-L98

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.Q_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) (hc : 0 ≤ c n α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ 1 := by sorry
