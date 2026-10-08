-- Prove2me | Theorems.Thm_RiskControl_UCB_theorem_1
-- name    : RiskControl.UCB.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:39.335059+00:00
-- url     : https://prove2.me/theorems/193180f4-ef14-4ee5-9b77-ffdfad9e5e2d
-- title:
--   Theorem 1, p. 5 — UCB calibration: with probability ≥ 1 − δ the selected λ̂ has R(λ̂) ≤ α
-- statement:
--   **Theorem 1 (Validity of UCB calibration).** Let $P$ be a probability distribution on $\mathcal X \times \mathcal Y$ and let $D = ((X_1, Y_1), \dots, (X_n, Y_n))$ be an i.i.d. sample from $P$. Let $\Lambda \subseteq \mathbb R \cup \{\pm\infty\}$ be closed and let $\{\mathcal T_\lambda\}$, $\mathcal T_\lambda : \mathcal X \to 2^{\mathcal Z}$, be nested on $\Lambda$:
--   $$\lambda_1 < \lambda_2 \implies \mathcal T_{\lambda_1}(x) \subseteq \mathcal T_{\lambda_2}(x). \tag{1}$$
--   Let $L(y, S) \ge 0$ be a loss with
--   $$S \subseteq S' \implies L(y, S) \ge L(y, S'), \tag{2}$$
--   such that $L(Y, \mathcal T_\lambda(X))$ is integrable for each $\lambda \in \Lambda$, and write $R(\lambda) = \mathbb E[L(Y, \mathcal T_\lambda(X))]$. Assume that $R(\lambda_{\max}) = 0$ for some $\lambda_{\max} \in \Lambda$ and that $R$ is continuous on $\Lambda$. Let $\widehat R^+(\lambda) = \widehat R^+(D, \lambda)$ be a function of the sample satisfying, for every $\lambda \in \Lambda$,
--   $$P^n\big(R(\lambda) \le \widehat R^+(\lambda)\big) \ge 1 - \delta, \tag{3}$$
--   and let $\hat\lambda = \inf\{\lambda \in \Lambda : \widehat R^+(\lambda') < \alpha \ \forall \lambda' \in \Lambda,\ \lambda' \ge \lambda\}$ as in (4). Then
--   $$P^n\big(R(\mathcal T_{\hat\lambda}) \le \alpha\big) \ge 1 - \delta,$$
--   that is, $\mathcal T_{\hat\lambda}$ is an $(\alpha, \delta)$-risk-controlling prediction set.
--
--   This is the paper's main guarantee: a confidence bound that holds for each fixed $\lambda$ separately suffices for the data-dependent choice $\hat\lambda$, with no uniform convergence, because the risk is monotone in $\lambda$.
--
--   **Formalization Note** The conclusion is written as a failure bound: the $P^n$-outer measure of the event "the set in (4) is nonempty and $R(\hat\lambda) > \alpha$" is at most $\delta$; for a measurable event this is the page's statement, and no measurability of $\widehat R^+$ or $\hat\lambda$ is assumed. When the set in (4) is empty, the page's $\hat\lambda = \inf\emptyset = +\infty$ need not lie in $\Lambda$ and $R(\mathcal T_{\hat\lambda})$ is undefined; that event is excluded (the safe output there is $\mathcal T_{\lambda_{\max}}$, of risk $0$). The space of predictions is $2^{\mathcal Z}$; $\Lambda$ is a closed subset of the extended reals and $R$ is continuous in its subspace topology. The integrability of the loss, the nonnegativity of $L$, the closedness of $\Lambda$ and the point $\lambda_{\max}$ are the standing assumptions of §2.1 (p. 4). The i.i.d. sample is the product measure $P^n$. The monotonicity of $R$ is not assumed; it follows from (1) and (2). No range is placed on $\alpha$ or $\delta$, as on the page.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Theorem 1, p. 5, in the setting of §2.1–2.2, p. 4, (1)–(4); proof p. 26 (via Theorem A.1)

import Mathlib
import Definitions.Def_RiskControl_UCB_Setting

open MeasureTheory

namespace RiskControl.UCB

/-- Theorem 1 (Validity of UCB calibration), arXiv:2101.02703v3, p. 5, in the setting of §2.1:
an i.i.d. calibration sample `D = ((X₁, Y₁), …, (Xₙ, Yₙ))` from `P`, a closed `Λ ⊆ ℝ ∪ {±∞}`,
nested set predictors (1), a nonnegative loss with (2), integrable losses, some `λ_max ∈ Λ`
with `R(λ_max) = 0`, a continuous risk, and a pointwise UCB (3). Then
`P(R(𝒯_λ̂) > α) ≤ δ` on the event that the calibration set of (4) is nonempty. -/
theorem theorem_1 {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P] (n : ℕ)
    (Λ : Set EReal) (hΛ : IsClosed Λ)
    (T : EReal → 𝒳 → Set 𝒵)
    (hnest : ∀ l₁ ∈ Λ, ∀ l₂ ∈ Λ, l₁ < l₂ → ∀ x, T l₁ x ⊆ T l₂ x)
    (L : 𝒴 → Set 𝒵 → ℝ) (hL0 : ∀ y S, 0 ≤ L y S)
    (hLmono : ∀ y S S', S ⊆ S' → L y S' ≤ L y S)
    (hint : ∀ l ∈ Λ, Integrable (fun p : 𝒳 × 𝒴 => L p.2 (T l p.1)) P)
    (hmax : ∃ lmax ∈ Λ, risk P L T lmax = 0)
    (hcont : ContinuousOn (risk P L T) Λ)
    (Rhat : (Fin n → 𝒳 × 𝒴) → EReal → ℝ) (α δ : ℝ)
    (hucb : ∀ l ∈ Λ,
      (Measure.pi fun _ : Fin n => P) {D | Rhat D l < risk P L T l} ≤ ENNReal.ofReal δ) :
    (Measure.pi fun _ : Fin n => P)
        {D | (calSet Λ (Rhat D) α).Nonempty ∧ α < risk P L T (lambdaHat Λ (Rhat D) α)}
      ≤ ENNReal.ofReal δ := by sorry

end RiskControl.UCB
