-- Prove2me | Theorems.Thm_Sendov_rev_rscale
-- name    : Sendov.rev_rscale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:48.783889+00:00
-- url     : https://prove2.me/theorems/7b262943-4dc0-4590-a791-3c41e51b0eba
-- title:
--   Sendov: rev rscale
-- statement:
--   The Sendov construction uses the rev rscale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L133-L140
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L133-L140

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.rev_rscale (g : List ℤ) (r : List (List ℤ)) (α t : ℝ) :
    rev (rscale g r) α t = pev g α * rev r α t := by sorry
