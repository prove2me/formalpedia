-- Prove2me | Theorems.Thm_Sendov_norm_deriv_add_le
-- name    : Sendov.norm_deriv_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:07.414334+00:00
-- url     : https://prove2.me/theorems/72cec22a-7b86-4865-93f7-f12e770101e2
-- title:
--   Sendov: norm deriv add le
-- statement:
--   **The pointwise estimate.**  `‖F'(t) + (n-1) a (x+iy) F(t)‖ ≤ a² t (n-1) β(t)^{(n-2)/2}`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L329-L358
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L329-L358

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.norm_deriv_add_le {n : ℕ} (hn : 2 ≤ n) {a x y t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (ha0 : 0 ≤ a) (ht0 : 0 ≤ t)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = (((n : ℝ) - 1) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
        + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
      ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by sorry
