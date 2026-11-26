-- Prove2me | Theorems.Thm_Sendov_continuous_prod_norm
-- name    : Sendov.continuous_prod_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:43.884231+00:00
-- url     : https://prove2.me/theorems/9dfb97ad-a8dc-50d7-9a65-2496e15391ed
-- title:
--   Sendov: continuous prod norm
-- statement:
--   The Sendov construction uses the continuous prod norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L197-L205
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L197-L205

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.continuous_prod_norm (a : ℝ) (q : Multiset ℂ) :
    Continuous fun t : ℝ =>
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by sorry
