-- Prove2me | Theorems.Thm_Sendov_sum_norm_le_card
-- name    : Sendov.sum_norm_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:23.164537+00:00
-- url     : https://prove2.me/theorems/46beccab-e089-5d97-85f1-41541f1f43ad
-- title:
--   Sendov: sum norm le card
-- statement:
--   The Sendov construction uses the sum norm le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L43-L54
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L43-L54

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.sum_norm_le_card : ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
    (q.map (fun v => ‖v‖)).sum ≤ (q.card : ℝ) := by sorry
