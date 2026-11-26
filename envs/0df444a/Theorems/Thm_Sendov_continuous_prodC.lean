-- Prove2me | Theorems.Thm_Sendov_continuous_prodC
-- name    : Sendov.continuous_prodC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:22.406489+00:00
-- url     : https://prove2.me/theorems/01651661-df65-58af-b45e-2aa837bb7c7c
-- title:
--   Sendov: continuous prod C
-- statement:
--   The Sendov construction uses the continuous prod C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L362-L369
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L362-L369

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.continuous_prodC (a : ℝ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod := by sorry
