-- Prove2me | Theorems.Thm_Sendov_one_le_tri
-- name    : Sendov.one_le_tri
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:13.090126+00:00
-- url     : https://prove2.me/theorems/3c80e4ae-9b64-437c-92e3-a900daa5d3d4
-- title:
--   Sendov: one le tri
-- statement:
--   **The triangle inequality `(tri)`.**  Integrating `norm_deriv_add_le` against the
--   fundamental theorem of calculus, using `F(0) = 1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L388-L452
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L388-L452

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.one_le_tri {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (ha0 : 0 ≤ a)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    1 ≤ ‖Fprod a q 1 + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)
            * ∫ t in (0 : ℝ)..1, Fprod a q t‖
        + a ^ 2 * ((n : ℝ) - 1)
            * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by sorry
