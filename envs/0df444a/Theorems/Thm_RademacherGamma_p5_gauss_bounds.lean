-- Prove2me | Theorems.Thm_RademacherGamma_p5_gauss_bounds
-- name    : RademacherGamma_p5_gauss_bounds
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:52:06.730309+00:00
-- url     : https://prove2.me/theorems/1c184dd2-0dc2-4bc0-8078-5378256d77e0
-- title:
--   Fifth-order Euler-Maclaurin bound for Gaussian difference series
-- statement:
--   Let $a_0 \in \mathbb{R}$, $\delta > 0$, and $t > 0$, and set $h(w) := e^{-(w - \delta)^2 t} - e^{-(w + \delta)^2 t}$, $h'(w) = -2(w-\delta)t e^{-(w-\delta)^2 t} + 2(w+\delta)t e^{-(w+\delta)^2 t}$, $f_3(u) := -4t^2 u (2u^2 t - 3) e^{-u^2 t}$, and $h'''(w) = f_3(w - \delta) - f_3(w + \delta)$. Then the series $\sum_{k=0}^\infty h(a_0 + \frac{1}{2} + k)$ is summable and satisfies the fifth-order Euler–Maclaurin bound
--
--   $$
--   \left|\sum_{k=0}^{\infty} h\!\left(a_0 + \frac{1}{2} + k\right) - \int_{a_0 - \delta}^{a_0 + \delta} e^{-v^2 t}\,dv - \frac{1}{24} h'(a_0) + \frac{7}{5760} h'''(a_0)\right| \le \frac{1}{24}\,(2\delta)\,t^2\sqrt{t}.
--   $$
--
--   This sharper estimate gives an $O(\delta t^{5/2})$ remainder for Gaussian difference series, essential for small-$t$ positivity estimates.
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

theorem RademacherGamma_p5_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) +
        2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
    let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
    |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) - (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
      (1 / 24) * h' a₀ + (7 / 5760) * h''' a₀| ≤ (1 / 24) * (2 * δ) * t ^ 2 * √t := by sorry
