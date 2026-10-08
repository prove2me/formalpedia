-- Prove2me | Theorems.Thm_RobustPower_StochGap_p14_mean_policy_feasible_for_symmetry_scenario
-- name    : RobustPower.StochGap.p14_mean_policy_feasible_for_symmetry_scenario
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:14:56.90971+00:00
-- url     : https://prove2.me/theorems/d1932caa-93be-4cde-8055-df220e4509dc
-- title:
--   P. 14, display after (2.11) — the mean second-stage decision is feasible for the central scenario
-- statement:
--   Let $\mu$ be a probability measure on the scenario set $\Omega$, let $b:\Omega\to\mathbb R^m$ be $\mu$-integrable, and let $\omega^0$ satisfy condition (2.1),
--   $$\mathbb E_\mu[b(\omega)]\ \ge\ b(\omega^0).$$
--   If $x$ and a $\mu$-integrable policy $y:\Omega\to\mathbb R^{n_2}_+$ satisfy $Ax+By(\omega)\ge b(\omega)$ for every $\omega$, then the mean decision $\bar y=\mathbb E_\mu[y(\omega)]$ is nonnegative and feasible for scenario $\omega^0$:
--   $$Ax+B\,\mathbb E_\mu[y(\omega)]\ \ge\ b(\omega^0).$$
--
--   This is the cost half of the proof of Theorem 2.1: it converts an expected cost into the cost of a single decision.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 14, display following (2.11)

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.StochGap

/-- P. 14, display after (2.11): if `x` and an integrable policy `y ≥ 0` satisfy
`A x + B y(ω) ≥ b(ω)` for every scenario, `b` is integrable and `E_μ[b(ω)] ≥ b(ω⁰)` (2.1), then
the mean policy `E_μ[y(ω)]` is a (nonnegative) feasible second-stage decision for scenario
`ω⁰`: `A x + B E_μ[y(ω)] ≥ b(ω⁰)`. -/
theorem p14_mean_policy_feasible_for_symmetry_scenario {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (hbint : Integrable b μ) (ω₀ : Ω)
    (hmean : b ω₀ ≤ ∫ ω, b ω ∂μ)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (hyint : Integrable y μ) (hy : ∀ ω, 0 ≤ y ω)
    (hfeas : ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y ω) :
    0 ≤ ∫ ω, y ω ∂μ ∧ b ω₀ ≤ A *ᵥ x + B *ᵥ (∫ ω, y ω ∂μ) := by sorry

end RobustPower.StochGap
