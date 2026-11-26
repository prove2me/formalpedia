-- Prove2me | Theorems.Thm_Sendov_gg0_length
-- name    : Sendov.gg0_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:00.627628+00:00
-- url     : https://prove2.me/theorems/57a651bd-463d-4f57-ac86-f1632851541f
-- title:
--   Sendov: gg0 length
-- statement:
--   The Sendov construction uses the gg0 length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L234-L234
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L234-L234

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.gg0_length (n : ℕ) : (gg0 n).length = 2 := by sorry

attribute [defeq] Sendov.gg0_length
