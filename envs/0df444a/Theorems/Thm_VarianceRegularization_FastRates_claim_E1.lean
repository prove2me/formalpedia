-- Prove2me | Theorems.Thm_VarianceRegularization_FastRates_claim_E1
-- name    : VarianceRegularization.FastRates.claim_E1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:04:17.652689+00:00
-- url     : https://prove2.me/theorems/6868877f-8480-42ef-b63e-c5059b012064
-- title:
--   Claim E.1, (42) — an approximate robust minimizer outside $S_\star^{2\epsilon}$ forces a large localized deviation
-- statement:
--   Assume the setting of Theorem 5: $\Theta\subseteq\mathbb R^d$ convex; $\ell(\cdot;x)$ convex and $L$-Lipschitz on $\Theta$ for every $x$ ($L\ge0$), with $\ell(\theta;\cdot)$ measurable and $P$-integrable; $S_\star$ nonempty and closed with projection $\pi$; and the growth condition (26) with $\lambda>0$, $\gamma>1$, $r>0$. Let $n\ge1$, $\rho\ge0$, $0<\epsilon\le\frac12\lambda r^\gamma$, and fix a sample $X_1,\dots,X_n$. If $\widehat S_\star^\epsilon\not\subset S_\star^{2\epsilon}$, then
--   $$\sup_{\theta\in S_\star^{2\epsilon}}\Big\{\Delta_n(\theta)+\sqrt{\frac{2\rho}{n}\mathrm{Var}_{\widehat P_n}\big(\ell(\theta;X)-\ell(\pi(\theta);X)\big)}\Big\}\ \ge\ \epsilon,$$
--   with $\Delta_n$ the localized empirical deviation (41).
--
--   The claim turns a failure of the inclusion $\widehat S_\star^\epsilon\subset S_\star^{2\epsilon}$, a statement about approximate minimizers of the robust risk, into a lower bound on a supremum of a centred empirical process over the fixed set $S_\star^{2\epsilon}$, which concentration inequalities can control.
--
--   **Formalization Note** The supremum is written as: for every $\delta>0$ there is $\theta\in S_\star^{2\epsilon}$ at which the bracket is at least $\epsilon-\delta$; this is equivalent to the supremum being at least $\epsilon$ and avoids the default value of a real supremum of an unbounded set. Condition (27) is not assumed.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 44, Claim E.1, inequality (42), with (41); proof pp. 45–46

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting
open MeasureTheory

namespace VarianceRegularization.FastRates

/-- Duchi–Namkoong, arXiv:1610.02581v3, Appendix E, p. 44, Claim E.1, inequality (42): under the
hypotheses of Theorem 5 other than (27), for every sample `s`, if `Ŝ_⋆^ε ⊄ S_⋆^{2ε}` then
`sup_{θ ∈ S_⋆^{2ε}} {Δ_n(θ) + √((2ρ/n) Var_{P̂_n}(ℓ(θ;X) − ℓ(π(θ);X)))} ≥ ε`.
The supremum is written without a real `⨆`: for every `δ > 0` some `θ ∈ S_⋆^{2ε}` brings the
bracket to at least `ε − δ` (equivalent to `sup ≥ ε`, the set being nonempty). -/
theorem claim_E1
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
    (s : Fin n → X) (hnot : ¬ empSubOptSet Θ ρ ℓ s ε ⊆ subOptSet Θ ℓ P (2 * ε)) :
    ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
      ε - δ ≤ localizedDeviation Θ ℓ P s θ
        + Real.sqrt (2 * ρ / n *
            empVar (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i))) := by sorry

end VarianceRegularization.FastRates
