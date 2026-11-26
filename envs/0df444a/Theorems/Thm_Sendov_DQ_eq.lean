-- Prove2me | Theorems.Thm_Sendov_DQ_eq
-- name    : Sendov.DQ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:05.882776+00:00
-- url     : https://prove2.me/theorems/ebaee456-d741-4b5d-a7ff-30d0cb75a5ba
-- title:
--   Sendov: DQ eq
-- statement:
--   The Sendov construction uses the DQ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L240-L251
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L240-L251

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.DQ_eq (n : ℕ) (hn : 2 ≤ n) (α t : ℝ) (hα : 0 ≤ α) :
    (2 * M n * (3 + α)) * Q n α t
      = pev (gg0 n) α + pev (gg1 n) α * t + pev (gg2 n) α * t ^ 2 := by sorry
