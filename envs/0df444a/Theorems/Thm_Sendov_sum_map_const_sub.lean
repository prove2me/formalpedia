-- Prove2me | Theorems.Thm_Sendov_sum_map_const_sub
-- name    : Sendov.sum_map_const_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:54:00.906931+00:00
-- url     : https://prove2.me/theorems/c97c8b4d-6f3c-50b1-93a1-0e5b9ffcacdb
-- title:
--   Sendov: sum map const sub
-- statement:
--   The Sendov construction uses the sum map const sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L48-L55
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L48-L55

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
set_option autoImplicit false
open Sendov

theorem Sendov.sum_map_const_sub (s : Multiset ℂ) (c : ℂ) (g : ℂ → ℂ) :
    (s.map (fun v => c - g v)).sum = (s.card : ℂ) * c - (s.map g).sum := by sorry
