-- Prove2me | Theorems.Thm_Sendov_bdig_add_mul
-- name    : Sendov.bdig_add_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:43.801539+00:00
-- url     : https://prove2.me/theorems/b87f917c-1eaa-40d7-a6fa-64bcb21b2d93
-- title:
--   Sendov: bdig add mul
-- statement:
--   The balanced digit of `c + b * N` is `c`, provided `2 * |c| < b`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L205-L223
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L205-L223

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.bdig_add_mul (b c N : ℤ) (hb : 0 < b) (hc : 2 * |c| < b) :
    bdig b (c + b * N) = c := by sorry
