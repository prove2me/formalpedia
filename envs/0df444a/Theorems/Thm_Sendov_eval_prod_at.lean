-- Prove2me | Theorems.Thm_Sendov_eval_prod_at
-- name    : Sendov.eval_prod_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:45.110323+00:00
-- url     : https://prove2.me/theorems/ac3fbbd5-337e-55b8-bc13-36da6786ca78
-- title:
--   Sendov: eval prod at
-- statement:
--   The Sendov construction uses the eval prod at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L56-L59
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L56-L59

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.eval_prod_at (u : ℂ) (s : Multiset ℂ) :
    ((s.map (fun w => X - C w)).prod).eval u = (s.map (fun w => u - w)).prod := by sorry
