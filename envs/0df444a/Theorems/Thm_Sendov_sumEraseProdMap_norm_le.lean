-- Prove2me | Theorems.Thm_Sendov_sumEraseProdMap_norm_le
-- name    : Sendov.sumEraseProdMap_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:06.420819+00:00
-- url     : https://prove2.me/theorems/c2d89417-a609-4909-938f-1b6e2ae321c3
-- title:
--   Sendov: sum Erase Prod Map norm le
-- statement:
--   **The error bound.**  `∑ⱼ ∏_{k≠j} ‖1 - a t q_k‖ ≤ (n-1) β(t)^{(n-2)/2}`: Maclaurin's
--   inequality, then Cauchy–Schwarz, then the quadratic mean.  Nonnegativity of `β(t)` is not
--   assumed — it follows from the quadratic-mean bound, `β(t)` dominating an average of squares.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L158-L233
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L158-L233

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.sumEraseProdMap_norm_le {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖)
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by sorry
