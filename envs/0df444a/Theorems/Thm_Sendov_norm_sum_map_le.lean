-- Prove2me | Theorems.Thm_Sendov_norm_sum_map_le
-- name    : Sendov.norm_sum_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:54:12.693376+00:00
-- url     : https://prove2.me/theorems/d4931bc6-33e0-4788-8321-b06e3c268d65
-- title:
--   Sendov: norm sum map le
-- statement:
--   The Sendov construction uses the norm sum map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L62-L68
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L62-L68

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
set_option autoImplicit false
open Sendov

theorem Sendov.norm_sum_map_le (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).sum‖ ≤ (s.map (fun w => ‖f w‖)).sum := by sorry
