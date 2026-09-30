-- Prove2me | Theorems.Thm_UnderstandingML_hoeffding_inequality
-- name    : UnderstandingML.hoeffding_inequality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:30:42.183745+00:00
-- url     : https://prove2.me/theorems/515dac95-e176-4993-93c6-dba9e13d3e65
-- title:
--   Lemma 4.5 (Hoeffding's inequality): P[|(1/m)∑θᵢ − μ| > ε] ≤ 2 exp(−2mε²/(b − a)²) for i.i.d. θᵢ ∈ [a, b] with mean μ
-- statement:
--   **Lemma 4.5 (Hoeffding's Inequality).** Let $\theta_1, \dots, \theta_m$ be a sequence of i.i.d. random variables and assume that for all $i$, $E[\theta_i] = \mu$ and $P[a \le \theta_i \le b] = 1$. Then, for any $\epsilon > 0$,
--   $$P\Big[\Big|\frac1m\sum_{i=1}^m \theta_i - \mu\Big| > \epsilon\Big] \le 2\exp\big(-2m\epsilon^2/(b-a)^2\big).$$
--
--   Formally: for a probability measure $D$ on $\Omega$, a measurable $\theta : \Omega \to \mathbb{R}$ with $a \le \theta \le b$ $D$-almost surely and mean $\mu = \int \theta\, dD$, and $\epsilon > 0$, the product law $D^m$ of the event $|\frac1m \sum_i \theta(\omega_i) - \mu| > \epsilon$ is at most $2\exp(-2m\epsilon^2/(b-a)^2)$ (when $a = b$ the bound reads $2$ under Lean's convention $x/0 = 0$ and is trivially true).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §4.2 p. 56, Lemma 4.5 (proved in Appendix B)

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 4.5 (Hoeffding's inequality)** (p. 56). Let `θ₁, …, θ_m` be a sequence of i.i.d. random
variables and assume that for all `i`, `E[θᵢ] = μ` and `P[a ≤ θᵢ ≤ b] = 1`. Then for any `ε > 0`,
`P[|(1/m) ∑ θᵢ − μ| > ε] ≤ 2 exp(−2mε²/(b − a)²)`. Stated on the product law of `m` copies of
a distribution `D` on `Ω`, for a measurable `θ : Ω → ℝ` with `a ≤ θ ≤ b` almost surely and mean
`μ = ∫ θ dD`. -/
theorem hoeffding_inequality {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω)
    [IsProbabilityMeasure D] (θ : Ω → ℝ) (hθ : Measurable θ) {a b : ℝ}
    (hab : ∀ᵐ ω ∂D, a ≤ θ ω ∧ θ ω ≤ b) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    iidLaw D m {ω | ε < |(∑ i, θ (ω i)) / m - ∫ x, θ x ∂D|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * m * ε ^ 2 / (b - a) ^ 2))) := by sorry

end UnderstandingML
