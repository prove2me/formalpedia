-- Prove2me | Theorems.Thm_Sendov_rev_radd
-- name    : Sendov.rev_radd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:41.336533+00:00
-- url     : https://prove2.me/theorems/70a73ea9-b09e-4b28-8354-3fb8f9afe4e1
-- title:
--   Sendov: rev radd
-- statement:
--   The Sendov construction uses the rev radd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L122-L131
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L122-L131

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.rev_radd (r s : List (List ℤ)) (α t : ℝ) :
    rev (radd r s) α t = rev r α t + rev s α t := by sorry
