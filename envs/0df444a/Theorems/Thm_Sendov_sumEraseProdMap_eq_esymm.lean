-- Prove2me | Theorems.Thm_Sendov_sumEraseProdMap_eq_esymm
-- name    : Sendov.sumEraseProdMap_eq_esymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:42.596279+00:00
-- url     : https://prove2.me/theorems/f48dd4c2-c750-557a-a5b1-cf996a46649c
-- title:
--   Sendov: sum Erase Prod Map eq esymm
-- statement:
--   The erasure form and `Multiset.esymm` agree, matched through their common recurrence.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L74-L85
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L74-L85

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.sumEraseProdMap_eq_esymm {α : Type*} : ∀ (s : Multiset α) (f : α → ℝ), s ≠ 0 →
    sumEraseProdMap s f = (s.map f).esymm ((s.map f).card - 1) := by sorry
