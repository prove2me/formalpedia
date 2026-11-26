-- Prove2me | Theorems.Thm_Sendov_gg2_length
-- name    : Sendov.gg2_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:58.665613+00:00
-- url     : https://prove2.me/theorems/a7c105f8-588b-5bb4-b7a1-8d60b2993af4
-- title:
--   Sendov: gg2 length
-- statement:
--   The Sendov construction uses the gg2 length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L238-L238
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L238-L238

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.gg2_length (n : ℕ) : (gg2 n).length = 3 := by sorry

attribute [defeq] Sendov.gg2_length
