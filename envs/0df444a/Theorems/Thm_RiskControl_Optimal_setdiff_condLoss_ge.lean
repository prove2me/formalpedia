-- Prove2me | Theorems.Thm_RiskControl_Optimal_setdiff_condLoss_ge
-- name    : RiskControl.Optimal.setdiff_condLoss_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:44.122424+00:00
-- url     : https://prove2.me/theorems/8e2b7b7b-820c-4850-b2f7-d87f19690a78
-- title:
--   Proof of Theorem 8, p. 27, displays 1–5 — R(T′) ≤ R(T_λ) ⟹ E∫_{T′(X)∖T_λ(X)} E[ℓ|X] dμ ≥ E∫_{T_λ(X)∖T′(X)} E[ℓ|X] dμ
-- statement:
--   In the setting of §4.3, let $P$ be the law of $(X, Y)$ on $\mathcal X \times \mathcal Y$ with marginal $P_X$, let $\kappa$ be a regular conditional distribution of $Y$ given $X$, let $\mu$ be a finite measure on $\mathcal Z$ and $\ell \ge 0$ measurable, and let $L(y; \mathcal S) = \int_{\mathcal S^c} \ell(y, z)\, d\mu(z)$ and $R(\mathcal T) = \mathbb E[L(Y; \mathcal T(X))]$. Let $\lambda < 0$, let $\mathcal T_\lambda(x) = \{z : \mathbb E[\ell(Y; z) \mid X = x] \ge -\lambda\}$ be the predictor (11), and let $\mathcal T'$ be a set-valued predictor with measurable graph such that $R(\mathcal T') \le R(\mathcal T_\lambda)$. Then
--   $$\mathbb E\Big[\int_{z \in \mathcal T'(X) \setminus \mathcal T_\lambda(X)} \mathbb E[\ell(Y; z) \mid X]\, d\mu(z)\Big] \ge \mathbb E\Big[\int_{z \in \mathcal T_\lambda(X) \setminus \mathcal T'(X)} \mathbb E[\ell(Y; z) \mid X]\, d\mu(z)\Big].$$
--
--   This is the fifth display of the proof of Theorem 8: the risk comparison, rewritten through the conditional expected cost, becomes a comparison over the two set differences.
--
--   **Formalization Note** The paper allows $\lambda \le 0$; the statement is posed for $\lambda < 0$, the range on which Theorem 8 holds (at $\lambda = 0$ Theorem 8 is false: with $\ell \equiv 0$, $\mathcal T_0(x) = \mathcal Z$ and $\mathcal T' \equiv \emptyset$ have equal risk $0$ but $\mathbb E|\mathcal T'(X)| = 0 < \mu(\mathcal Z)$). The page passes from the first to the third display by subtracting $\mathbb E\int_{\mathcal Z} \mathbb E[\ell(Y; z) \mid X]\, d\mu(z)$, which may be infinite; the conclusion stated here is the page's fifth display, which holds without any finiteness assumption on $\ell$ because $R(\mathcal T_\lambda) \le -\lambda\, \mu(\mathcal Z) < \infty$. The regular conditional distribution is a Markov kernel $\kappa$ with $P = P_X \otimes \kappa$; $\mathcal T'$ is required to have a measurable graph, which the page leaves implicit.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Theorem 8, p. 27, first to fifth displays; (11), p. 13

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RiskControl.Optimal

/-- Proof of Theorem 8, arXiv:2101.02703v3, p. 27, displays 1–5: if `λ < 0`, `𝒯′` has a measurable
graph and `R(𝒯′) ≤ R(𝒯_λ)` with `𝒯_λ` of (11), then
`𝔼[∫_{z ∈ 𝒯_λ(X) ∖ 𝒯′(X)} 𝔼[ℓ(Y; z) | X] dμ(z)] ≤ 𝔼[∫_{z ∈ 𝒯′(X) ∖ 𝒯_λ(X)} 𝔼[ℓ(Y; z) | X] dμ(z)]`. -/
theorem setdiff_condLoss_ge {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (lam : ℝ) (hlam : lam < 0)
    (T' : 𝒳 → Set 𝒵) (hT' : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ T' q.1})
    (hR : risk P μ ℓ T' ≤ risk P μ ℓ (thresholdSet κ ℓ lam)) :
    ∫⁻ x, ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, condLoss κ ℓ x z ∂μ ∂P.fst
      ≤ ∫⁻ x, ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ ∂P.fst := by sorry

end RiskControl.Optimal
