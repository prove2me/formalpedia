-- Prove2me | Theorems.Thm_Sendov_one_le_integral_prod_norm
-- name    : Sendov.one_le_integral_prod_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:03:18.34684+00:00
-- url     : https://prove2.me/theorems/79d1f851-8327-5b89-b876-0c297e85c5f4
-- title:
--   Sendov: one le integral prod norm
-- statement:
--   **The branch point `(⋆)`.**  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.
--
--   The high-degree argument relaxes this by AM–GM to the raw polar inequality; the low-degree
--   argument bounds each factor by `a + (1-a²)t`.  It is stated separately so that neither route
--   has to reproduce the other's work.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L115-L153
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L115-L153

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.one_le_integral_prod_norm {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by sorry
