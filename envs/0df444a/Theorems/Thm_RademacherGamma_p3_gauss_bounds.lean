-- Prove2me | Theorems.Thm_RademacherGamma_p3_gauss_bounds
-- name    : RademacherGamma_p3_gauss_bounds
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:51:07.259897+00:00
-- url     : https://prove2.me/theorems/906e1303-4071-4df0-b290-d7c2f7d2a710
-- title:
--   Third-order Euler-Maclaurin bound for Gaussian difference series
-- statement:
--   Let $a_0 \in \mathbb{R}$, $\delta > 0$, and $t > 0$, and define $h(w) := e^{-(w - \delta)^2 t} - e^{-(w + \delta)^2 t}$ with derivative $h'(w) = -2(w - \delta)t e^{-(w - \delta)^2 t} + 2(w + \delta)t e^{-(w + \delta)^2 t}$. Then the series $\sum_{k=0}^\infty h(a_0 + \frac{1}{2} + k)$ is summable and satisfies the third-order Euler–Maclaurin error estimate
--
--   $$
--   \left|\sum_{k=0}^{\infty} h\!\left(a_0 + \frac{1}{2} + k\right) - \int_{a_0 - \delta}^{a_0 + \delta} e^{-v^2 t}\,dv - \frac{1}{24} h'(a_0)\right| \le \frac{11}{60}\,(2\delta)\,t\sqrt{t}.
--   $$
--
--   This third-order bound provides a uniform $O(\delta t^{3/2})$ remainder estimate for shifted Gaussian difference sums via the periodic Bernoulli kernel $P_3$.
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

theorem RademacherGamma_p3_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) + 2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
      |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) -
        (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) - (1 / 24) * h' a₀| ≤
        (11 / 60) * (2 * δ) * t * √t := by sorry
