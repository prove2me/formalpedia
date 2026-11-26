-- Prove2me | Theorems.Thm_Sendov_Q_nonneg
-- name    : Sendov.Q_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:34.58527+00:00
-- url     : https://prove2.me/theorems/80771e9b-202d-441a-add7-21736a41a968
-- title:
--   Sendov: Q nonneg
-- statement:
--   The Sendov construction uses the Q nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L66-L68
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L66-L68

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.Q_nonneg (hfeas : c n α ^ 2 ≤ A n α) (t : ℝ) : 0 ≤ Q n α t := by sorry
