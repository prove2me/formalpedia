-- Prove2me | Theorems.Thm_Sendov_beta_prod
-- name    : Sendov.beta_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:20.625034+00:00
-- url     : https://prove2.me/theorems/15b53a11-2f7e-4233-9626-4c52346472ed
-- title:
--   Sendov: beta prod
-- statement:
--   The sharp Beta constant, factored.  This is the cancellation that makes `T1` rational:
--   `(r+1)(r+2)(r+3)(r+4) = (n-2) n (n+2)(n+4)/16` at `r = (n-4)/2`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L159-L163
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L159-L163

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.beta_prod (n : ℕ) :
    (((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
        * (((n : ℝ) - 4) / 2 + 4)
      = ((n : ℝ) - 2) * (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) / 16 := by sorry
