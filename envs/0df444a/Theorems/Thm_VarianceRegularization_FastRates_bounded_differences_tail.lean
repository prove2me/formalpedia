-- Prove2me | Theorems.Thm_VarianceRegularization_FastRates_bounded_differences_tail
-- name    : VarianceRegularization.FastRates.bounded_differences_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:04:26.993544+00:00
-- url     : https://prove2.me/theorems/addcc6b5-dfbb-4a2e-95b9-6861f3503a9d
-- title:
--   Appendix E, p. 45 — bounded-differences tail of $\sup_{S_\star^{2\epsilon}}\Delta_n$ above $2\mathbb E[\mathfrak R_n(S_\star^{2\epsilon})]$
-- statement:
--   Assume the setting of Theorem 5 with $L>0$ ($\Theta$ convex; $\ell(\cdot;x)$ convex and $L$-Lipschitz on $\Theta$; $\ell(\theta;\cdot)$ measurable and integrable; $S_\star$ nonempty and closed; growth condition (26) with $\lambda>0$, $\gamma>1$, $r>0$), let $n\ge1$ and $0<\epsilon\le\frac12\lambda r^\gamma$, and let $X_1,\dots,X_n$ be i.i.d. from $P$. Write $\mathbb E[\mathfrak R_n(S_\star^{2\epsilon})]$ for the expectation over the sample of the empirical Rademacher complexity of the localized class over $S_\star^{2\epsilon}$. Then for every $u\ge0$,
--   $$\mathbb P\Big(\sup_{\theta\in S_\star^{2\epsilon}}\Delta_n(\theta)\ \ge\ 2\mathbb E[\mathfrak R_n(S_\star^{2\epsilon})]+u\Big)\ \le\ \exp\Big(-\frac{nu^2}{2L^2}\Big(\frac{\lambda}{2\epsilon}\Big)^{2/\gamma}\Big).$$
--
--   This is the concentration step of the proof of Theorem 5: symmetrization bounds the mean of the supremum by twice the expected Rademacher complexity, and the bounded-differences inequality controls its fluctuations, with differences of order $\frac{2L}{n}(2\epsilon/\lambda)^{1/\gamma}$ by the localization of $S_\star^{2\epsilon}$.
--
--   **Formalization Note** The page calls the deviation $t$; it is renamed $u$ to keep it apart from the $t$ of Theorem 5. The map from samples to $\mathfrak R_n(S_\star^{2\epsilon})$ is assumed integrable, so that the expectation is the true one and not the default value $0$ of a non-integrable Bochner integral. "$\sup\ge c$" is written as: for every $\delta>0$ some $\theta\in S_\star^{2\epsilon}$ reaches $c-\delta$. $L>0$ is assumed because the bound divides by $L^2$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 45, display following the bounded-differences computation (citing Boucheron–Lugosi–Massart, Theorem 6.5)

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting
open MeasureTheory

namespace VarianceRegularization.FastRates

/-- Duchi–Namkoong, arXiv:1610.02581v3, Appendix E, p. 45, the display after the
bounded-differences computation: under the hypotheses of Theorem 5 with `L > 0`, for all
`u ≥ 0` (the page's `t`, renamed to keep it apart from the `t` of Theorem 5),
`ℙ(sup_{θ ∈ S_⋆^{2ε}} Δ_n(θ) ≥ 2 𝔼[𝔑_n(S_⋆^{2ε})] + u) ≤ exp(−(n u²/(2L²)) (λ/(2ε))^{2/γ})`.
`𝔼[𝔑_n(S_⋆^{2ε})]` is the expectation over the sample of the empirical Rademacher complexity
of the localized class, assumed integrable so that the Bochner integral is the true expectation.
"`sup ≥ c`" is written as "for every `δ > 0` some `θ ∈ S_⋆^{2ε}` reaches `c − δ`". -/
theorem bounded_differences_tail
{X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hlip : ∀ x, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, |ℓ θ x - ℓ θ' x| ≤ L * ‖θ - θ'‖)
    (hmeas : ∀ θ ∈ Θ, Measurable (ℓ θ)) (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (hS_ne : (subOptSet Θ ℓ P 0).Nonempty) (hS_closed : IsClosed (subOptSet Θ ℓ P 0))
    (lam γ r : ℝ) (hlam : 0 < lam) (hγ : 1 < γ) (hr : 0 < r)
    (hgrowth : ∀ θ ∈ Θ, Metric.infDist θ (subOptSet Θ ℓ P 0) ≤ r →
      ∀ θs ∈ subOptSet Θ ℓ P 0,
        lam * Metric.infDist θ (subOptSet Θ ℓ P 0) ^ γ ≤ risk ℓ P θ - risk ℓ P θs)
    (hLpos : 0 < L) (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (hRint : Integrable (fun s : Fin n → X => localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s)
      (Measure.pi (fun _ : Fin n => P)))
    (u : ℝ) (hu : 0 ≤ u) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
          2 * (∫ s', localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s'
                ∂(Measure.pi (fun _ : Fin n => P))) + u - δ
            ≤ localizedDeviation Θ ℓ P s θ}
      ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * u ^ 2 / (2 * L ^ 2)) * (lam / (2 * ε)) ^ (2 / γ))) := by sorry

end VarianceRegularization.FastRates
