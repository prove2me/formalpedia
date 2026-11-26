-- Prove2me | Theorems.Thm_Sendov_sum_norm_sq_one_sub_le
-- name    : Sendov.sum_norm_sq_one_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:40.141851+00:00
-- url     : https://prove2.me/theorems/e788d65d-faff-5467-b704-9ddfae1e0481
-- title:
--   Sendov: sum norm sq one sub le
-- statement:
--   `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, where `β(t) = 1 - 2 a x t + a² t²`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L110-L128
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L110-L128

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.sum_norm_sq_one_sub_le {n : ℕ} {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hn : 1 ≤ n)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ ^ 2)).sum
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by sorry
