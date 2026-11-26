-- Prove2me | Theorems.Thm_Sendov_sum_le_card_mul
-- name    : Sendov.sum_le_card_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:42.938606+00:00
-- url     : https://prove2.me/theorems/27215c34-3665-5d3d-9721-69c87e3f1ff2
-- title:
--   Sendov: sum le card mul
-- statement:
--   The Sendov construction uses the sum le card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L111-L122
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L111-L122

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.sum_le_card_mul (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, x ≤ c) →
    s.sum ≤ (s.card : ℝ) * c := by sorry
