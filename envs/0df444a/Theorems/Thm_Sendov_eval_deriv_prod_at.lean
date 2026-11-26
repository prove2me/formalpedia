-- Prove2me | Theorems.Thm_Sendov_eval_deriv_prod_at
-- name    : Sendov.eval_deriv_prod_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:34.22099+00:00
-- url     : https://prove2.me/theorems/65ca4159-5edc-45e6-ba3e-6615ed3a9c01
-- title:
--   Sendov: eval deriv prod at
-- statement:
--   The Sendov construction uses the eval deriv prod at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L61-L71
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L61-L71

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.eval_deriv_prod_at (u : ℂ) : ∀ (s : Multiset ℂ),
    (derivative (s.map (fun w => X - C w)).prod).eval u
      = sumEraseProd (s.map (fun w => u - w)) := by sorry
