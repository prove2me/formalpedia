-- Prove2me | Theorems.Thm_Sendov_sum_map_sub
-- name    : Sendov.sum_map_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:59.656787+00:00
-- url     : https://prove2.me/theorems/2fe5fd96-853a-5f99-b279-0514caff77bd
-- title:
--   Sendov: sum map sub
-- statement:
--   The Sendov construction uses the sum map sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L40-L46
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L40-L46

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
set_option autoImplicit false
open Sendov

theorem Sendov.sum_map_sub (s : Multiset ℂ) (f g : ℂ → ℂ) :
    (s.map (fun v => f v - g v)).sum = (s.map f).sum - (s.map g).sum := by sorry
