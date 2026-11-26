-- Prove2me | Theorems.Thm_Sendov_mem_le_npev_one
-- name    : Sendov.mem_le_npev_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:07.792284+00:00
-- url     : https://prove2.me/theorems/76f129ec-36c4-44e9-8744-5c5ca2fd3c2a
-- title:
--   Sendov: mem le npev one
-- statement:
--   Every coefficient is at most the sum of the coefficients, which is the value at `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L145-L155
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L145-L155

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.mem_le_npev_one : ∀ (q : List ℕ) (a : ℕ), a ∈ q → a ≤ npev q 1 := by sorry
