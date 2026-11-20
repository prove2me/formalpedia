-- Prove2me | Theorems.Thm_RademacherGamma_gaussian_sum_ge_c2_box
-- name    : RademacherGamma_gaussian_sum_ge_c2_box
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:52:07.63397+00:00
-- url     : https://prove2.me/theorems/e03b6367-2817-4a87-8fdb-99e4738ebf5f
-- title:
--   Verified box-tree lower bound for Gaussian difference series (Case 2)
-- statement:
--   Let $y, \eta, t \in \mathbb{R}$ satisfy $\frac{1}{4} \le y \le \frac{9}{5}$, $0 < \eta \le \frac{1}{4}$, $\frac{7}{10} < t \le 4$, and $2(y - \eta)^2 t < 3$. Then
--
--   $$
--   2\!\left(\frac{1}{2} - \eta\right) e^{-y^2 t} \le \sum_{k=0}^{\infty} \left(e^{-(y + k - (1/2 - \eta))^2 t} - e^{-(y + k + (1/2 - \eta))^2 t}\right).
--   $$
--
--   This resolves the compact intermediate box of Case 2 ($1/4 < \delta < 1/2$, with $\eta = 1/2 - \delta$) via verified branch-and-bound.
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

theorem RademacherGamma_gaussian_sum_ge_c2_box {y η t : ℝ}
    (hy : 1 / 4 ≤ y) (hy_hi : y ≤ 18 / 10)
    (hη0 : 0 < η) (hη_le : η ≤ 1 / 4)
    (ht_lo : 7 / 10 < t) (ht_hi : t ≤ 4)
    (h2b_neg : 2 * (y - η) ^ 2 * t < 3) :
    2 * (1 / 2 - η) * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - (1 / 2 - η)) ^ 2 * t) -
        Real.exp (-(y + k + (1 / 2 - η)) ^ 2 * t)) := by sorry
