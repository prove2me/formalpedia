-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_lemma_1
-- name    : PersonalizedRM.RevenueGap.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:52.535555+00:00
-- url     : https://prove2.me/theorems/76934c84-90cc-4fdc-b17f-eae099a378c7
-- title:
--   Lemma 1, p. 15 — ‖∇ℓ_n(θ∗)‖_∞ ≤ √(2 log(2nJ(d + 1))/n) with probability ≥ 1 − 1/n
-- statement:
--   Assume the personalized logit model with Assumption 1, with true parameter $\theta^*$ and $n \ge 1$ samples. Then, with probability at least $1 - 1/n$, every partial derivative of the negative log-likelihood at the true parameter is small:
--
--   $$\|\nabla \ell_n(\theta^*)\|_\infty = \max_{j,k} \Big|\frac{\partial \ell_n}{\partial \theta_{jk}}(\theta^*)\Big| \ \le\ \sqrt{\frac{2\log(2nJ(d+1))}{n}} .$$
--
--   Under well-specification the gradient of $\ell_n$ at $\theta^*$ is an average of mean-zero bounded terms, which is why it concentrates at the rate $\sqrt{\log n / n}$. This bound and the strong convexity of Lemma 2 are the two inputs of Theorem 1.
--
--   **Formalization Note.** The page says "under the assumptions of Theorem 1"; the statement here assumes only Assumption 1 and $n \ge 1$, since Assumption 2 and the sample-size threshold are not used by the proof (pp. ec1–ec2); this is a strengthening. The hypothesis $n \ge 1$ is added because $1/n$ is $0$ in Lean at $n = 0$. The statement bounds the (outer) probability of the event that some partial derivative exceeds the threshold. Partial derivatives are `fderiv` applied to the coordinate vectors of `EuclideanSpace`.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. 15, Lemma 1; proof pp. ec1–ec2, (EC.3)

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Lemma 1 (Gradient Bound), p. 15: with probability at least `1 − 1/n`,
`‖∇ℓ_n(θ∗)‖_∞ ≤ √(2 log(2nJ(d + 1))/n)`. Stated as an upper bound on the (outer) measure of the
bad event. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n J d : ℕ} (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
    (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
    (θstar : Param J d) (pmin ψ : ℝ) (hn : 0 < n)
    (hA1 : Assumption1 P S z price u y θstar pmin ψ) :
    P {ω | ¬ ∀ j k, |fderiv ℝ (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω))
        θstar (EuclideanSpace.single (j, k) 1)| ≤
          Real.sqrt (2 * Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) / n)}
      ≤ ENNReal.ofReal (1 / n) := by sorry

end PersonalizedRM.RevenueGap
