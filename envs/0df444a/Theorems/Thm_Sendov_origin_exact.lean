-- Prove2me | Theorems.Thm_Sendov_origin_exact
-- name    : Sendov.origin_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:05:27.809333+00:00
-- url     : https://prove2.me/theorems/ad98a5a7-dac1-48db-bac6-4347368370ff
-- title:
--   Sendov: origin exact
-- statement:
--   **`(origin-exact)`.**  The origin channel, in the form the reduction consumes.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L179-L254
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L179-L254

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.origin_exact {n : ℕ} (hn : 5 ≤ n) {a x y α : ℝ} {z q : Multiset ℂ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I))
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hfirst : (n : ℂ) * ∫ t in (0 : ℝ)..1, Fprod a q t = (-1) ^ (n - 1) * q.prod * z.prod)
    (hsecond : (n : ℂ) * (q.map (fun v => 1 - (a : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z))
    (hα : α = M n * (1 - a ^ 2) / 2) :
    2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by sorry
