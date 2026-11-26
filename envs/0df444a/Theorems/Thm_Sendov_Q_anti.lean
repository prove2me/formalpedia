-- Prove2me | Theorems.Thm_Sendov_Q_anti
-- name    : Sendov.Q_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:52.514904+00:00
-- url     : https://prove2.me/theorems/b6e798c4-bb8f-5f1e-9d46-e9fdda6b70f8
-- title:
--   Sendov: Q anti
-- statement:
--   `Q` decreases with `n` on `[0,1]`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L72-L91
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L72-L91

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
set_option autoImplicit false
open Sendov
variable {α t : ℝ}

theorem Sendov.Q_anti {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ Q m α t := by sorry
