-- Prove2me | Theorems.Thm_Sendov_rev_cons
-- name    : Sendov.rev_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:54.044578+00:00
-- url     : https://prove2.me/theorems/a6efc095-a195-4ab9-a3df-558a0da34df3
-- title:
--   Sendov: rev cons
-- statement:
--   The Sendov construction uses the rev cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L119-L120
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L119-L120

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.rev_cons (p : List ℤ) (r : List (List ℤ)) (α t : ℝ) :
    rev (p :: r) α t = pev p α + t * rev r α t := by sorry

attribute [defeq] Sendov.rev_cons
