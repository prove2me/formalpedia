-- Prove2me | Theorems.Thm_RiskControl_UCB_theorem_A_1
-- name    : RiskControl.UCB.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:29.393367+00:00
-- url     : https://prove2.me/theorems/1049c7f5-06f2-45ea-a4a7-38f8d2866259
-- title:
--   Theorem A.1, p. 26 — UCB calibration for any continuous nonincreasing R: P(R(λ̂) ≤ α) ≥ 1 − δ
-- statement:
--   **Theorem A.1 (Validity of UCB calibration, abstract form).** Let $(\Omega, \mathcal F, \mu)$ be a probability space, let $\Lambda \subseteq \overline{\mathbb R}$ be closed, and let $R : \overline{\mathbb R} \to \mathbb R$ be continuous and nonincreasing on $\Lambda$, with $R(\lambda) \le \alpha$ for some $\lambda \in \Lambda$. Let $\widehat R^+ : \Omega \times \overline{\mathbb R} \to \mathbb R$ satisfy the pointwise upper confidence bound
--   $$\mu\big(\widehat R^+(\lambda) < R(\lambda)\big) \le \delta \qquad \text{for every } \lambda \in \Lambda, \tag{3}$$
--   and let $\hat\lambda(\omega) = \inf\{\lambda \in \Lambda : \widehat R^+(\omega, \lambda') < \alpha \ \forall \lambda' \in \Lambda,\ \lambda' \ge \lambda\}$ as in (4). Then
--   $$\mu\Big(\{\omega : \text{the set in (4) is nonempty and } R(\hat\lambda(\omega)) > \alpha\}\Big) \le \delta,$$
--   that is, $R(\hat\lambda) \le \alpha$ with probability at least $1 - \delta$.
--
--   It is the abstract engine behind Theorem 1 and the later calibration theorems of the paper: any family of predictors with a monotone continuous risk and any pointwise confidence bound yield a risk-controlling choice of $\lambda$.
--
--   **Formalization Note** The page's conclusion reads $P(R(\lambda) \le \alpha) \ge 1 - \delta$; the statement and proof are about $\hat\lambda$, which is what is stated here. "With probability at least $1-\delta$" is written as a failure probability at most $\delta$, measured by $\mu$ as an outer measure, so no measurability of $\widehat R^+$ or of $\hat\lambda$ is assumed (for a measurable event this is the page's statement; dropping "$\widehat R^+(\lambda)$ is a random variable" only strengthens the result). When the set in (4) is empty, $\hat\lambda = +\infty$ need not lie in $\Lambda$ and $R(\hat\lambda)$ is not defined on the page; the event is restricted to a nonempty set. No range is placed on $\alpha$ or $\delta$, as on the page.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Theorem A.1, p. 26 (conclusion read with λ̂ for the printed λ)

import Mathlib
import Definitions.Def_RiskControl_UCB_Setting

open MeasureTheory

namespace RiskControl.UCB

/-- Theorem A.1 (Validity of UCB calibration, abstract form), arXiv:2101.02703v3, p. 26, with
the conclusion about `λ̂` (the page prints `λ`). `R : Λ → ℝ` is continuous and nonincreasing on
`Λ` with `R(λ) ≤ α` for some `λ ∈ Λ`; `R̂⁺(λ)` satisfies (3) pointwise; then the event
"the calibration set of (4) is nonempty and `R(λ̂) > α`" has (outer) probability at most `δ`. -/
theorem theorem_A_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Λ : Set EReal) (hΛ : IsClosed Λ) (R : EReal → ℝ)
    (hanti : AntitoneOn R Λ) (hcont : ContinuousOn R Λ) (α δ : ℝ)
    (hex : ∃ l ∈ Λ, R l ≤ α) (Rhat : Ω → EReal → ℝ)
    (hucb : ∀ l ∈ Λ, μ {ω | Rhat ω l < R l} ≤ ENNReal.ofReal δ) :
    μ {ω | (calSet Λ (Rhat ω) α).Nonempty ∧ α < R (lambdaHat Λ (Rhat ω) α)}
      ≤ ENNReal.ofReal δ := by sorry

end RiskControl.UCB
