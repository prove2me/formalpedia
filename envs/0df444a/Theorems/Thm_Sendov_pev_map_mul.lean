-- Prove2me | Theorems.Thm_Sendov_pev_map_mul
-- name    : Sendov.pev_map_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:18.548799+00:00
-- url     : https://prove2.me/theorems/61ebc274-8574-4e04-b5aa-53db55930be9
-- title:
--   Sendov: pev map mul
-- statement:
--   The Sendov construction uses the pev map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L84-L91
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L84-L91

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.pev_map_mul (a : ℤ) (q : List ℤ) (x : ℝ) :
    pev (q.map (fun b => a * b)) x = (a : ℝ) * pev q x := by sorry
