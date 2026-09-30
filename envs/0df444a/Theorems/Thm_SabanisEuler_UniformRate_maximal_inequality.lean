-- Prove2me | Theorems.Thm_SabanisEuler_UniformRate_maximal_inequality
-- name    : SabanisEuler.UniformRate.maximal_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T03:53:36.712302+00:00
-- url     : https://prove2.me/theorems/e18de885-f79c-46b6-846f-df18f005177b
-- title:
--   Lemma 5 — Gyöngy–Krylov maximal inequality for dominated processes
-- statement:
--   Let $(\Omega,\mathcal F,\{\mathcal F_t\}_{t\ge0},P)$ be a filtered probability space with right-continuous filtration, and let $T\in[0,\infty)$. Let $f=(f_t)_{t\in[0,T]}$ and $g=(g_t)_{t\in[0,T]}$ be nonnegative, $\{\mathcal F_t\}$-adapted processes with continuous paths on $[0,T]$. Suppose that for every constant $c>0$ and every stopping time $\tau\le T$,
--   $$\mathbb E\big[f_\tau\mathbb 1_{\{g_0\le c\}}\big]\le\mathbb E\big[g_\tau\mathbb 1_{\{g_0\le c\}}\big].$$
--   Then for every stopping time $\tau\le T$ and every $\gamma\in(0,1)$,
--   $$\mathbb E\Big[\sup_{t\le\tau}f_t^{\gamma}\Big]\le\frac{2-\gamma}{1-\gamma}\,\mathbb E\Big[\sup_{t\le\tau}g_t^{\gamma}\Big].$$
--
--   This is a Lenglart-type domination inequality: a bound on expectations at stopping times upgrades to a bound on the expected running maximum, at the price of a fractional power $\gamma<1$. In the proof of Theorem 3 it turns an Itô-formula estimate for $\mathbb E[(\varphi(\tau)|X(\tau)-X_n(\tau)|^2)^{p/2}]$ at stopping times into a bound on the expected supremum over $[0,T]$.
--
--   **Formalization Note** Nonnegativity is built into the value type $[0,\infty)$; expectations are Lebesgue integrals in $[0,\infty]$, so both sides may be $+\infty$. Stopping times take values in $[0,\infty]$ and are required to satisfy $\tau\le T$ everywhere. Nothing is required of $f,g$ after $T$. The process $g$ is not assumed nondecreasing, and the right-hand side is $\mathbb E[\sup_{t\le\tau}g_t^{\gamma}]$, as printed. The right-continuity of the filtration is the paper's standing usual condition; completeness of the filtration is not imposed.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 19, Lemma 5 (citing Gyöngy–Krylov)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace SabanisEuler.UniformRate

/-- Sabanis (2016), arXiv:1308.1796v4, p. 19, Lemma 5 (the Gyöngy–Krylov / Lenglart-type
maximal inequality). Let `T ∈ [0, ∞)` and let `f = (f_t)_{t ∈ [0, T]}`,
`g = (g_t)_{t ∈ [0, T]}` be nonnegative `ℱ`-adapted processes with continuous paths on
`[0, T]` such that, for every constant `c > 0` and every stopping time `τ ≤ T`,
`𝔼[f_τ 𝟙_{g₀ ≤ c}] ≤ 𝔼[g_τ 𝟙_{g₀ ≤ c}]`. Then for every stopping time `τ ≤ T` and every
`γ ∈ (0, 1)`,
`𝔼[sup_{t ≤ τ} f_t^γ] ≤ (2 - γ)/(1 - γ) · 𝔼[sup_{t ≤ τ} g_t^γ]`.
Nonnegativity is built into the value type `ℝ≥0`; expectations are lower Lebesgue integrals
in `[0, ∞]`. Nothing is required of `f`, `g` after `T`. `g` is not assumed nondecreasing,
and the right-hand side is `sup_{t ≤ τ} g_t^γ`, as printed. -/
theorem maximal_inequality
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (T : ℝ≥0)
    (f g : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (hg_cont : ∀ ω, ContinuousOn (fun t => g t ω) (Set.Icc 0 T))
    (hf_adapt : ∀ t ≤ T, Measurable[ℱ t] (f t))
    (hg_adapt : ∀ t ≤ T, Measurable[ℱ t] (g t))
    (hdom : ∀ c : ℝ≥0, 0 < c → ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ →
      (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue f τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P
        ≤ ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue g τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P) :
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ → (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∀ γ : ℝ, 0 < γ → γ < 1 →
        ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞) ^ γ) ∂P
          ≤ ENNReal.ofReal ((2 - γ) / (1 - γ)) *
            ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞) ^ γ) ∂P := by sorry

end SabanisEuler.UniformRate
