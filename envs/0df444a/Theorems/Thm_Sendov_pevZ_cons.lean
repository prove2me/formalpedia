-- Prove2me | Theorems.Thm_Sendov_pevZ_cons
-- name    : Sendov.pevZ_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:12.461293+00:00
-- url     : https://prove2.me/theorems/5a687c6c-77c5-5dd4-bb52-dfd1730f5c65
-- title:
--   Sendov: pev Z cons
-- statement:
--   The Sendov construction uses the pev Z cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L187-L188
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L187-L188

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.pevZ_cons (a : ℤ) (p : List ℤ) (b : ℤ) :
    pevZ (a :: p) b = a + b * pevZ p b := by sorry

attribute [defeq] Sendov.pevZ_cons
