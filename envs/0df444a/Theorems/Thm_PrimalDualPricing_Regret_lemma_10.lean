-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_10
-- name    : PrimalDualPricing.Regret.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:01.255165+00:00
-- url     : https://prove2.me/theorems/71a5fade-1df6-4844-a1cf-0477e38d57de
-- title:
--   Lemma 10, p. 25 — $\mathbb E|X-\lambda|\le\sqrt\lambda$ for $X\sim\mathrm{Poisson}(\lambda)$
-- statement:
--   Let $X$ be a Poisson random variable with mean $\lambda\ge0$. Then $|X-\lambda|$ is integrable and
--   $$\mathbb E\big[|X-\lambda|\big]\le\sqrt\lambda.$$
--
--   The analysis uses it to bound the expected deviation of the sales from their mean in the last phase (Lemma 8 and Propositions 2–3).
--
--   **Formalization Note** The law of $X$ is Mathlib's `poissonMeasure λ` on $\mathbb N$. Integrability is part of the conclusion, so the bound cannot hold through Lean's convention that the integral of a non-integrable function is $0$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 25, Appendix B, Lemma 10

import Mathlib

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 10 (Chen–Gallego, arXiv:1812.09234v3, p. 25). If `X` is Poisson with mean `λ ≥ 0`, then
`|X − λ|` is integrable and `E[|X − λ|] ≤ √λ`. -/
theorem lemma_10 (lam : NNReal) :
    Integrable (fun x : ℕ => |(x : ℝ) - lam|) (poissonMeasure lam) ∧
    ∫ x, |(x : ℝ) - lam| ∂(poissonMeasure lam) ≤ Real.sqrt lam := by sorry

end PrimalDualPricing.Regret
