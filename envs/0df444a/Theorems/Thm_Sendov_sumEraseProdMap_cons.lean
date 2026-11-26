-- Prove2me | Theorems.Thm_Sendov_sumEraseProdMap_cons
-- name    : Sendov.sumEraseProdMap_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:33.735433+00:00
-- url     : https://prove2.me/theorems/3e04a2cd-4134-4236-9998-8f70667917af
-- title:
--   Sendov: sum Erase Prod Map cons
-- statement:
--   The Sendov construction uses the sum Erase Prod Map cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L64-L71
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L64-L71

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov
open scoped Classical

theorem Sendov.sumEraseProdMap_cons {α : Type*} (v : α) (t : Multiset α) (f : α → ℝ) :
    sumEraseProdMap (v ::ₘ t) f = (t.map f).prod + f v * sumEraseProdMap t f := by sorry
