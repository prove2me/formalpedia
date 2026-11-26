-- Prove2me | Theorems.Thm_Sendov_npev_ppowN
-- name    : Sendov.npev_ppowN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:05.660702+00:00
-- url     : https://prove2.me/theorems/1f823978-4b84-4ee8-a553-3b08c2c97ece
-- title:
--   Sendov: npev ppow N
-- statement:
--   The Sendov construction uses the npev ppow N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L137-L140
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L137-L140

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.npev_ppowN (p : List ℕ) (b k : ℕ) : npev (ppowN p k) b = npev p b ^ k := by sorry
