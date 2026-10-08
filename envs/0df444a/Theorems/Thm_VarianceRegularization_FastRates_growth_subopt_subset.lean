-- Prove2me | Theorems.Thm_VarianceRegularization_FastRates_growth_subopt_subset
-- name    : VarianceRegularization.FastRates.growth_subopt_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:04:09.716318+00:00
-- url     : https://prove2.me/theorems/eae2206e-df0d-49f3-ba77-1cef3ac32f72
-- title:
--   Appendix E, p. 44 — the growth condition confines $S_\star^{2\epsilon}$ to a $(2\epsilon/\lambda)^{1/\gamma}$-neighbourhood of $S_\star$
-- statement:
--   Let $\Theta\subseteq\mathbb R^d$ be convex, let $\ell(\cdot;x)$ be convex and $L$-Lipschitz on $\Theta$ for every $x$, with $\ell(\theta;\cdot)$ measurable and $P$-integrable for $\theta\in\Theta$, and let the solution set $S_\star$ of $\min_\Theta R$ be nonempty and closed, with Euclidean projection $\pi=\pi_{S_\star}$. Let $\lambda>0$, $\gamma>1$, $r>0$, and assume the growth condition (26):
--   $$R(\theta)-\inf_{\Theta}R\ \ge\ \lambda\,\mathrm{dist}(\theta,S_\star)^\gamma\quad\text{for all }\theta\in\Theta\text{ with }\mathrm{dist}(\theta,S_\star)\le r.$$
--   Then for every $0\le\epsilon\le\frac12\lambda r^\gamma$,
--   $$S_\star^{2\epsilon}\subset\Big\{\theta\in\Theta:\|\theta-\pi(\theta)\|_2\le\Big(\frac{2\epsilon}{\lambda}\Big)^{1/\gamma}\Big\}=\Big\{\theta\in\Theta:\mathrm{dist}(\theta,S_\star)\le\Big(\frac{2\epsilon}{\lambda}\Big)^{1/\gamma}\Big\}.$$
--
--   This is the deterministic localization step of the proof of Theorem 5: the growth condition, though assumed only within distance $r$ of $S_\star$, controls the size of every $2\epsilon$-suboptimal point, which bounds the localized process uniformly.
--
--   **Formalization Note** The growth condition is stated with $R(\theta^\star)$ for an arbitrary $\theta^\star\in S_\star$ in place of $\inf_\Theta R$ (the same number, $S_\star$ being nonempty). $S_\star$ nonempty and closed are the presuppositions of the projection (Appendix E calls $S_\star$ "a closed convex set").
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 44, Appendix E, display after Claim E.1; hypotheses of Theorem 5, p. 19, eq. (26)

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting
open MeasureTheory

namespace VarianceRegularization.FastRates

/-- Duchi–Namkoong, arXiv:1610.02581v3, Appendix E, p. 44 (display after Claim E.1): under the
hypotheses of Theorem 5 (convexity, the growth condition (26)) and `0 ≤ ε ≤ ½ λ r^γ`,
`S_⋆^{2ε} ⊂ {θ ∈ Θ : ‖θ − π(θ)‖₂ ≤ (2ε/λ)^{1/γ}} = {θ ∈ Θ : dist(θ, S_⋆) ≤ (2ε/λ)^{1/γ}}`.
`S_⋆` is assumed nonempty and closed, as presupposed by the projection `π = π_{S_⋆}`. -/
theorem growth_subopt_subset
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
    (ε : ℝ) (hε : 0 ≤ ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ) :
    subOptSet Θ ℓ P (2 * ε) ⊆
        {θ | θ ∈ Θ ∧ ‖θ - proj (subOptSet Θ ℓ P 0) θ‖ ≤ (2 * ε / lam) ^ (1 / γ)} ∧
      {θ | θ ∈ Θ ∧ ‖θ - proj (subOptSet Θ ℓ P 0) θ‖ ≤ (2 * ε / lam) ^ (1 / γ)} =
        {θ | θ ∈ Θ ∧ Metric.infDist θ (subOptSet Θ ℓ P 0) ≤ (2 * ε / lam) ^ (1 / γ)} := by sorry

end VarianceRegularization.FastRates
