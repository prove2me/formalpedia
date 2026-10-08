-- Prove2me | Theorems.Thm_VarianceRegularization_FastRates_deviation_event_bound
-- name    : VarianceRegularization.FastRates.deviation_event_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:04:17.33845+00:00
-- url     : https://prove2.me/theorems/d44a60d6-8095-414f-98b4-891bede59be2
-- title:
--   Appendix E, (43) — failure of the inclusion implies $\sup_{S_\star^{2\epsilon}}\Delta_n\ge\epsilon/2$
-- statement:
--   Assume the setting of Theorem 5 ($\Theta$ convex; $\ell(\cdot;x)$ convex and $L$-Lipschitz on $\Theta$, $L\ge0$; $\ell(\theta;\cdot)$ measurable and integrable; $S_\star$ nonempty and closed; growth condition (26) with $\lambda>0$, $\gamma>1$, $r>0$), let $n\ge1$, $\rho\ge0$, $0<\epsilon\le\frac12\lambda r^\gamma$, and assume the first condition of (27):
--   $$\epsilon\ \ge\ \Big(2\frac{8^\gamma L^\gamma}{\lambda}\Big)^{\frac1{\gamma-1}}\Big(\frac\rho n\Big)^{\frac{\gamma}{2(\gamma-1)}}.$$
--   Then:
--
--   1. for every sample, if the event (42) of Claim E.1 holds then $\sup_{\theta\in S_\star^{2\epsilon}}\Delta_n(\theta)\ge\epsilon/2$;
--   2. for an i.i.d. sample from $P$,
--   $$\mathbb P\big(\widehat S_\star^\epsilon\not\subset S_\star^{2\epsilon}\big)\ \le\ \mathbb P\Big(\sup_{\theta\in S_\star^{2\epsilon}}\Delta_n(\theta)\ge\frac\epsilon2\Big).$$
--
--   The first condition of (27) makes the variance term of (42) at most $\epsilon/2$ on $S_\star^{2\epsilon}$, so the probability of a misplaced approximate robust minimizer is reduced to a tail probability of the supremum of $\Delta_n$.
--
--   **Formalization Note** Each "$\sup\ge c$" is written as: for every $\delta>0$ some $\theta\in S_\star^{2\epsilon}$ reaches $c-\delta$. Probabilities are the product measure $P^{\otimes n}$ of the sets of samples (the outer measure if a set is not measurable). The constant is the printed one; the proof on p. 45 uses the condition $\epsilon\ge(8L^2\rho/n)^{\gamma/(2(\gamma-1))}(2/\lambda)^{1/(\gamma-1)}$, which the printed condition implies.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 45, inequality (43) and the display before it; condition (27), p. 19

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting
open MeasureTheory

namespace VarianceRegularization.FastRates

/-- Duchi–Namkoong, arXiv:1610.02581v3, Appendix E, p. 45, inequality (43) and the display
before it: under the hypotheses of Theorem 5 and the first condition of (27),
(i) for every sample, the event (42) implies `sup_{θ ∈ S_⋆^{2ε}} Δ_n(θ) ≥ ε/2`, and
(ii) `ℙ(Ŝ_⋆^ε ⊄ S_⋆^{2ε}) ≤ ℙ(sup_{θ ∈ S_⋆^{2ε}} Δ_n(θ) ≥ ε/2)`.
Each "`sup ≥ c`" is written as "for every `δ > 0` some `θ ∈ S_⋆^{2ε}` reaches `c − δ`"; the
probabilities are the (outer) measure `P^{⊗n}` of the sample sets. -/
theorem deviation_event_bound
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
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε) :
    (∀ s : Fin n → X,
      (∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
        ε - δ ≤ localizedDeviation Θ ℓ P s θ
          + Real.sqrt (2 * ρ / n *
              empVar (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i)))) →
      ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε), ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ) ∧
    Measure.pi (fun _ : Fin n => P) {s | ¬ empSubOptSet Θ ρ ℓ s ε ⊆ subOptSet Θ ℓ P (2 * ε)}
      ≤ Measure.pi (fun _ : Fin n => P)
          {s | ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
            ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ} := by sorry

end VarianceRegularization.FastRates
