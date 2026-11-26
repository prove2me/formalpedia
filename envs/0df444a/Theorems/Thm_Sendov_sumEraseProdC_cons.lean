-- Prove2me | Theorems.Thm_Sendov_sumEraseProdC_cons
-- name    : Sendov.sumEraseProdC_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:21.627373+00:00
-- url     : https://prove2.me/theorems/a068c326-e778-5d4f-bd1b-60bd9564efda
-- title:
--   Sendov: sum Erase Prod C cons
-- statement:
--   The Sendov construction uses the sum Erase Prod C cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L249-L257
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L249-L257

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov
open scoped Classical

theorem Sendov.sumEraseProdC_cons (v : ℂ) (t : Multiset ℂ) (g f : ℂ → ℂ) :
    sumEraseProdC (v ::ₘ t) g f = g v * (t.map f).prod + f v * sumEraseProdC t g f := by sorry
