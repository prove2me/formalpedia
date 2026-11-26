-- Prove2me | Theorems.Thm_Sendov_npev_pmulN
-- name    : Sendov.npev_pmulN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:02.847182+00:00
-- url     : https://prove2.me/theorems/68a6bf2d-1d62-49fc-9427-10696c0a5d3c
-- title:
--   Sendov: npev pmul N
-- statement:
--   The Sendov construction uses the npev pmul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L129-L135
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L129-L135

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.npev_pmulN (p q : List ℕ) (b : ℕ) :
    npev (pmulN p q) b = npev p b * npev q b := by sorry
