-- Prove2me | Theorems.Thm_Sendov_Q_eq
-- name    : Sendov.Q_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:38.509386+00:00
-- url     : https://prove2.me/theorems/bbea832c-fe6d-4ccc-bf7e-4fcd6cc32f50
-- title:
--   Sendov: Q eq
-- statement:
--   `Q` written as a sum of squares.  Compare `β(t) = (1 - a x t) ^ 2 + a² t² (1 - x²)`
--   in the blog post.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L36-L39
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L36-L39

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.Q_eq (n : ℕ) (α t : ℝ) :
    Q n α t = (1 - c n α * t) ^ 2 + (A n α - c n α ^ 2) * t ^ 2 := by sorry
