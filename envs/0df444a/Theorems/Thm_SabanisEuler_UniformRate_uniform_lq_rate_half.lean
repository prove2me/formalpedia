-- Prove2me | Theorems.Thm_SabanisEuler_UniformRate_uniform_lq_rate_half
-- name    : SabanisEuler.UniformRate.uniform_lq_rate_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T04:10:29.410773+00:00
-- url     : https://prove2.me/theorems/b85144bf-a2ac-4061-9e23-ad1d3a545460
-- title:
--   Theorem 3 — uniform Lq-convergence of the tamed Euler scheme with order 1/2
-- statement:
--   Let $(\Omega,\{\mathcal F_t\}_{t\ge0},\mathcal F,P)$ be a filtered probability space with right-continuous filtration, $W$ a $d_1$-dimensional Wiener martingale, $T>0$, and $p_0,p_1\ge2$. Let $b:[0,\infty)\times\mathbb R^d\to\mathbb R^d$ and $\sigma:[0,\infty)\times\mathbb R^d\to\mathbb R^{d\times d_1}$ be Borel, and let $X(0)$ be $\mathcal F_0$-measurable. Suppose A-2, A-4, A-5 and A-6 (with exponent $l$) hold, and that $p$ satisfies the $\mathfrak p$-condition:
--   $$l\le\frac{p_0-2}{4},\qquad 0<p<p_1,\qquad p\le\frac{p_0}{2l+1}.$$
--   Suppose moreover that $p_1>2$. Let $X$ solve the SDE (2.1) on $[0,T]$, and for every $n\ge1$ let $X_n$ solve the scheme (2.2) with the tamed coefficients (2.11)–(2.12) with $\alpha=1/2$,
--   $$b_n(t,x)=\frac{b(t,x)}{1+n^{-1/2}|x|^l},\qquad\sigma_n(t,x)=\frac{\sigma(t,x)}{1+n^{-1/2}|x|^l},$$
--   driven by the same $W$ and started at the same $X(0)$. Then for every $0<q<p$ there is a constant $C$, independent of $n$, such that for every $n\ge1$,
--   $$\mathbb E\Big[\sup_{0\le t\le T}|X(t)-X_n(t)|^q\Big]\le Cn^{-q/2}.$$
--
--   The theorem gives the optimal strong rate $1/2$ of Euler-type approximations, now uniformly in time inside the expectation, for SDEs whose drift and diffusion coefficients may grow superlinearly. It strengthens the pointwise-in-time $\mathcal L^p$ rate of Theorem 2 at the cost of lowering the moment from $p$ to any $q<p$.
--
--   **Formalization Note** The hypothesis $p_1>2$ is added to the printed statement. The printed proof applies Itô's formula to $(\varphi(t)|X(t)-X_n(t)|^2)^{p/2}$ for $p>2$ (and $p=2$); an admissible $p<2$ is handled through $p'=2$, which satisfies the $\mathfrak p$-condition exactly when $p_1>2$. At $p_1=2$ the paper's argument proves nothing. The exponent is restricted to $q>0$, the paper's $\mathcal L^q$ convention. The constant $C$ may depend on $q$ and all data except $n$. Expectation and supremum are computed in $[0,\infty]$; the supremum sits inside the expectation. Solutions are hypotheses: the theorem applies to any solution $X$ and any family $(X_n)$ on one probability space.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 6, Theorem 3, eq. (2.14)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_Shared_Conditions
import Definitions.Def_SabanisEuler_Shared_Model2

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.UniformRate

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 6, Theorem 3, eq. (2.14): under A-2, A-4–A-6 and
the 𝔭-condition (the scheme (2.2) uses the tamed coefficients (2.11)–(2.12) with `α = 1/2`,
`l ≤ (p₀ - 2)/4`, `0 < p < p₁`, `p ≤ p₀/(2l + 1)`), the scheme converges to the solution of
(2.1) in uniform `𝓛^q` with order 1/2: for every `0 < q < p` there is a constant `C`
independent of `n` with `𝔼[sup_{0 ≤ t ≤ T} |X(t) - Xₙ(t)|^q] ≤ C n^{-q/2}` for every
`n ≥ 1`. The supremum is inside the expectation.
**Added hypothesis:** `2 < p₁` (`hp₁2`). The printed proof applies Itô's formula to
`(φ(t)|X - Xₙ|²)^{p/2}` for `p > 2` (and `p = 2`); an admissible `p < 2` is handled through
`p' = 2`, which the 𝔭-condition admits exactly when `p₁ > 2`. At `p₁ = 2` the paper's
argument proves nothing. `0 < q` is the paper's `𝓛^q` convention. -/
theorem uniform_lq_rate_half
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ p₁ : ℝ) (hp₀ : 2 ≤ p₀) (hp₁ : 2 ≤ p₁) (hp₁2 : 2 < p₁)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (l : ℝ)
    (hA2 : CondA2 T b) (hA4 : CondA4 T p₀ b σ) (hA5 : CondA5 P p₀ ξ)
    (hA6 : CondA6 T p₁ l b σ)
    (p : ℝ) (hp : PCondition p₀ p₁ l p)
    (X : ℝ≥0 → Ω → SDEState d) (hX : IsSolution P ℱ W T ξ b σ X)
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n →
      IsSchemeSolution P ℱ W T ξ (tamedDrift (1 / 2) l b) (tamedDiffusion (1 / 2) l σ) n (Xₙ n)) :
    ∀ q : ℝ, 0 < q → q < p → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ‖X t ω - Xₙ n t ω‖ₑ ^ q) ∂P)
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(q / 2))) := by sorry

end SabanisEuler.UniformRate
