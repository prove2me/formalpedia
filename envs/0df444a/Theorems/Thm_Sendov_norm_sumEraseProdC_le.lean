-- Prove2me | Theorems.Thm_Sendov_norm_sumEraseProdC_le
-- name    : Sendov.norm_sumEraseProdC_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:11.532306+00:00
-- url     : https://prove2.me/theorems/acfa5242-0a1f-4fa9-ac7f-34ee8757d295
-- title:
--   Sendov: norm sum Erase Prod C le
-- statement:
--   A weighted erasure sum with unit-size weights is dominated by the unweighted one.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L260-L273
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L260-L273

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.norm_sumEraseProdC_le (g f : ℂ → ℂ) : ∀ (s : Multiset ℂ), (∀ v ∈ s, ‖g v‖ ≤ 1) →
    ‖sumEraseProdC s g f‖ ≤ sumEraseProdMap s (fun v => ‖f v‖) := by sorry
