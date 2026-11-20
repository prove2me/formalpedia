-- Prove2me | Theorems.Thm_RademacherGamma_gaussian_sum_ge_c1_box
-- name    : RademacherGamma_gaussian_sum_ge_c1_box
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:52:06.713792+00:00
-- url     : https://prove2.me/theorems/489ea9c4-8d23-4fc0-94b1-05cb179515f3
-- title:
--   Verified box-tree lower bound for Gaussian difference series (Case 1)
-- statement:
--   Let $y, \delta, t \in \mathbb{R}$ satisfy $\frac{1}{4} \le y \le \frac{11}{10}$, $0 < \delta \le \frac{1}{4}$, $\frac{7}{10} < t \le 3$, together with $yt < \frac{3}{4}$ and $2(y - \delta)^2 t < 1$. Then
--
--   $$
--   2\delta e^{-y^2 t} \le \sum_{k=0}^{\infty} \left(e^{-(y + k - \delta)^2 t} - e^{-(y + k + \delta)^2 t}\right).
--   $$
--
--   This covers the compact intermediate regime of Case 1 ($0 < \delta \le 1/4$) in Rademacher's Gamma-ratio monotonicity proof.
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

theorem RademacherGamma_gaussian_sum_ge_c1_box {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hy_hi : y ≤ 11 / 10)
    (hδ0 : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (ht_lo : 7 / 10 < t) (ht_hi : t ≤ 3)
    (h1a_neg : y * t < 3 / 4) (h1b_neg : 2 * (y - δ) ^ 2 * t < 1) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) := by sorry
