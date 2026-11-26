-- Prove2me | Theorems.Thm_Sendov_unpackN_pow
-- name    : Sendov.unpackN_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:57.970078+00:00
-- url     : https://prove2.me/theorems/2ceb6d21-01bf-47e2-8b80-f2f5f17d6a01
-- title:
--   Sendov: unpack N pow
-- statement:
--   **Kronecker substitution.**  The coefficients of `p ^ k` are recovered from the single
--   natural number `(npev p b) ^ k`, provided the base `b` exceeds every coefficient of `p ^ k`
--   — for which `(npev p 1) ^ k < b` suffices, `npev p 1` being the sum of the coefficients.
--
--   This is the statement that lets the kernel replace `Θ(k³)` interpreted list steps by one
--   GMP-backed exponentiation.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L163-L170
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L163-L170

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.unpackN_pow (b : ℕ) (hb : 0 < b) (p : List ℕ) (k : ℕ)
    (hbound : npev p 1 ^ k < b) :
    unpackN b (ppowN p k).length (npev p b ^ k) = ppowN p k := by sorry
