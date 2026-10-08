-- Prove2me | Theorems.Thm_RiskControl_UCB_risk_antitone
-- name    : RiskControl.UCB.risk_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:49.095748+00:00
-- url     : https://prove2.me/theorems/9c0a7770-20b8-4e9c-bf33-2c64fba7c703
-- title:
--   §2.1, pp. 4–5 — under nesting (1) and loss monotonicity (2), the risk λ ↦ R(λ) is nonincreasing on Λ
-- statement:
--   Let $P$ be a measure on $\mathcal X \times \mathcal Y$, let $\Lambda \subseteq \overline{\mathbb R}$, and let $\{\mathcal T_\lambda\}$ be a family of set-valued predictors $\mathcal T_\lambda : \mathcal X \to 2^{\mathcal Z}$ that is **nested** on $\Lambda$,
--   $$\lambda_1 < \lambda_2 \implies \mathcal T_{\lambda_1}(x) \subseteq \mathcal T_{\lambda_2}(x) \quad (\lambda_1, \lambda_2 \in \Lambda,\ x \in \mathcal X), \tag{1}$$
--   and let $L$ be a loss on sets satisfying
--   $$S \subseteq S' \implies L(y, S) \ge L(y, S'). \tag{2}$$
--   Suppose that $(x, y) \mapsto L(y, \mathcal T_\lambda(x))$ is $P$-integrable for every $\lambda \in \Lambda$. Then the risk $R(\lambda) = \mathbb E[L(Y, \mathcal T_\lambda(X))]$ is nonincreasing on $\Lambda$:
--   $$\lambda_1, \lambda_2 \in \Lambda,\ \lambda_1 \le \lambda_2 \implies R(\lambda_2) \le R(\lambda_1).$$
--
--   This monotonicity of the risk is what lets the paper turn a pointwise confidence bound into a guarantee for the data-driven choice $\hat\lambda$ (p. 5); Theorem A.1 assumes it, and Theorem 1 obtains it from (1) and (2).
--
--   **Formalization Note** The paper names this property on p. 5 without a separate statement. The integrability hypothesis is needed because the Bochner integral returns $0$ for a non-integrable integrand.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, §2.1, (1), (2) and the risk R(𝒯), p. 4; monotonicity of the risk named on p. 5, paragraph after Theorem 1

import Mathlib
import Definitions.Def_RiskControl_UCB_Setting

open MeasureTheory

namespace RiskControl.UCB

/-- §2.1, pp. 4–5: under the nesting property (1) of `{𝒯_λ}` and the monotonicity (2) of the
loss, the risk `λ ↦ R(λ)` is nonincreasing on `Λ`. -/
theorem risk_antitone {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (P : Measure (𝒳 × 𝒴)) (Λ : Set EReal)
    (T : EReal → 𝒳 → Set 𝒵)
    (hnest : ∀ l₁ ∈ Λ, ∀ l₂ ∈ Λ, l₁ < l₂ → ∀ x, T l₁ x ⊆ T l₂ x)
    (L : 𝒴 → Set 𝒵 → ℝ)
    (hLmono : ∀ y S S', S ⊆ S' → L y S' ≤ L y S)
    (hint : ∀ l ∈ Λ, Integrable (fun p : 𝒳 × 𝒴 => L p.2 (T l p.1)) P) :
    AntitoneOn (risk P L T) Λ := by sorry

end RiskControl.UCB
