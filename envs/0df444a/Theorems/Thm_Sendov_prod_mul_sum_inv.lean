-- Prove2me | Theorems.Thm_Sendov_prod_mul_sum_inv
-- name    : Sendov.prod_mul_sum_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:54:39.283845+00:00
-- url     : https://prove2.me/theorems/daad362f-30da-5cce-9b63-485248a1378f
-- title:
--   Sendov: prod mul sum inv
-- statement:
--   `(∏ s) ∑ⱼ 1/sⱼ = ∑ⱼ ∏_{k≠j} sₖ`, the clearing of denominators that is valid exactly when
--   no `sⱼ` vanishes.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L83-L93
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L83-L93

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
set_option autoImplicit false
open Sendov

theorem Sendov.prod_mul_sum_inv : ∀ (s : Multiset ℂ), (∀ w ∈ s, w ≠ 0) →
    s.prod * (s.map (fun w => w⁻¹)).sum = sumEraseProd s := by sorry
