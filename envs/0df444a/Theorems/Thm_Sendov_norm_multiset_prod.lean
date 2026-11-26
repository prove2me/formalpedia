-- Prove2me | Theorems.Thm_Sendov_norm_multiset_prod
-- name    : Sendov.norm_multiset_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:19.026279+00:00
-- url     : https://prove2.me/theorems/f1625bbd-436e-4961-9878-f7105d840070
-- title:
--   Sendov: norm multiset prod
-- statement:
--   The Sendov construction uses the norm multiset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L75-L78
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L75-L78

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by sorry
