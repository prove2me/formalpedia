-- Prove2me | Theorems.Thm_Sendov_rev_qrow
-- name    : Sendov.rev_qrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:43.758038+00:00
-- url     : https://prove2.me/theorems/b0db1b51-523a-5c26-8057-deb4cb3b3dfb
-- title:
--   Sendov: rev qrow
-- statement:
--   The Sendov construction uses the rev qrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L158-L164
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L158-L164

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.rev_qrow (g₀ g₁ g₂ : List ℤ) (k : ℕ) (α t : ℝ) :
    rev (qrow g₀ g₁ g₂ k) α t = (pev g₀ α + pev g₁ α * t + pev g₂ α * t ^ 2) ^ k := by sorry
