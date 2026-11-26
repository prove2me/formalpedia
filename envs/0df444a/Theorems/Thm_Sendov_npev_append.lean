-- Prove2me | Theorems.Thm_Sendov_npev_append
-- name    : Sendov.npev_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:07.232225+00:00
-- url     : https://prove2.me/theorems/bad2c31b-11aa-4e82-91ca-d00507b2f0fa
-- title:
--   Sendov: npev append
-- statement:
--   Evaluation of a concatenation: the second block is shifted by `b ^ (length of the
--   first)`.  This is what makes the two-dimensional packing work.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L84-L90
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L84-L90

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.npev_append (p q : List ℕ) (b : ℕ) :
    npev (p ++ q) b = npev p b + b ^ p.length * npev q b := by sorry
