-- Prove2me | Theorems.Thm_RademacherGamma_gaussian_sum_ge_2b_p3
-- name    : RademacherGamma_gaussian_sum_ge_2b_p3
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T11:17:29.21703+00:00
-- url     : https://prove2.me/theorems/a0200477-0d19-42c9-bd63-d870b384db72
-- title:
--   Small-t Euler-Maclaurin lower bound for Gaussian difference series (Case 2)
-- statement:
--   Let $y, \eta, t \in \mathbb{R}$ satisfy $y \ge \frac{1}{4}$, $0 < \eta \le \frac{1}{4}$, $0 < t \le \frac{7}{10}$, and $2(y - \eta)^2 t < 3$. Then
--
--   $$
--   2\!\left(\frac{1}{2} - \eta\right) e^{-y^2 t} \le \sum_{k=0}^{\infty} \left(e^{-(y + k - (1/2 - \eta))^2 t} - e^{-(y + k + (1/2 - \eta))^2 t}\right).
--   $$
--
--   This resolves the small-$t$ regime of Case 2 ($1/4 < \delta < 1/2$, with $\eta = 1/2 - \delta$) via fifth-order Euler–Maclaurin summation.
-- source:
--   LL_Decomp530a.leaf_rademacher_gamma_ratio (Rademacher Gamma-ratio inequality helper)

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Real MeasureTheory Filter Set
open scoped Topology

theorem RademacherGamma_gaussian_sum_ge_2b_p3 {y η t : ℝ}
    (hy : 1 / 4 ≤ y) (hη0 : 0 < η) (hη_le : η ≤ 1 / 4) (ht : 0 < t)
    (ht_ub : t ≤ 7 / 10) (h2b : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by sorry
