-- Prove2me | Theorems.Thm_Sendov_gg1_length
-- name    : Sendov.gg1_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:02.531076+00:00
-- url     : https://prove2.me/theorems/f1573b35-c289-4f6a-8bb9-49e4add71960
-- title:
--   Sendov: gg1 length
-- statement:
--   The Sendov construction uses the gg1 length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L236-L236
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L236-L236

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.gg1_length (n : ℕ) : (gg1 n).length = 3 := by sorry

attribute [defeq] Sendov.gg1_length
