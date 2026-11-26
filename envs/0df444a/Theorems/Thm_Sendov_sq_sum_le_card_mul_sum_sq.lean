-- Prove2me | Theorems.Thm_Sendov_sq_sum_le_card_mul_sum_sq
-- name    : Sendov.sq_sum_le_card_mul_sum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:17.86681+00:00
-- url     : https://prove2.me/theorems/01f0aa91-f4b2-434e-b73e-85d85d83c41d
-- title:
--   Sendov: sq sum le card mul sum sq
-- statement:
--   The Sendov construction uses the sq sum le card mul sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L132-L153
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L132-L153

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    (s.sum) ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by sorry
