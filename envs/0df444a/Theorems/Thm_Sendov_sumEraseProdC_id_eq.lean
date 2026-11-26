-- Prove2me | Theorems.Thm_Sendov_sumEraseProdC_id_eq
-- name    : Sendov.sumEraseProdC_id_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:23.955555+00:00
-- url     : https://prove2.me/theorems/13d22024-4776-4df0-adf6-03fc14ccc57d
-- title:
--   Sendov: sum Erase Prod C id eq
-- statement:
--   Splitting the derivative sum into its main term and its residual:
--   `∑ⱼ qⱼ ∏_{k≠j}(1-atq_k) = (∑ⱼ qⱼ) F(t) + a t ∑ⱼ qⱼ² ∏_{k≠j}(1-atq_k)`, since
--   `1 - (1 - a t qⱼ) = a t qⱼ`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L285-L296
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L285-L296

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.sumEraseProdC_id_eq (a t : ℝ) : ∀ (q : Multiset ℂ),
    sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
      = q.sum * Fprod a q t
        + (a : ℂ) * (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
            (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by sorry
