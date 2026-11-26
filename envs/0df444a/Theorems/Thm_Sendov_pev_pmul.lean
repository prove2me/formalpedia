-- Prove2me | Theorems.Thm_Sendov_pev_pmul
-- name    : Sendov.pev_pmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:27.247723+00:00
-- url     : https://prove2.me/theorems/c06388bb-aba9-4b84-a9b3-27690f7c4bb2
-- title:
--   Sendov: pev pmul
-- statement:
--   The Sendov construction uses the pev pmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L93-L99
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L93-L99

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.pev_pmul (p q : List ℤ) (x : ℝ) : pev (pmul p q) x = pev p x * pev q x := by sorry
