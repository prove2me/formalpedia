-- Prove2me | Theorems.Thm_Sendov_pev_cons
-- name    : Sendov.pev_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:39.235386+00:00
-- url     : https://prove2.me/theorems/21344b21-4427-5527-a4be-51f99849a0fb
-- title:
--   Sendov: pev cons
-- statement:
--   The Sendov construction uses the pev cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L70-L71
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L70-L71

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.pev_cons (a : ℤ) (p : List ℤ) (x : ℝ) :
    pev (a :: p) x = (a : ℝ) + x * pev p x := by sorry

attribute [defeq] Sendov.pev_cons
