-- Prove2me | Theorems.Thm_Roberts1997_RWM_expect_min_one_exp_gaussian
-- name    : Roberts1997.RWM.expect_min_one_exp_gaussian
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:47:55.428906+00:00
-- url     : https://prove2.me/theorems/99f9eb4b-e81a-4206-bf00-5cdaf96f5918
-- title:
--   Proposition 2.4 — 𝔼[1 ∧ e^A] = Φ(μ/σ) + exp(μ + σ²/2)Φ(−σ − μ/σ) for A ~ N(μ, σ²)
-- statement:
--   Let $\mu\in\mathbb R$, $\sigma>0$ and $A\sim N(\mu,\sigma^2)$. With $\Phi$ the standard normal distribution function,
--
--   $$ \mathbb E\big[1\wedge e^A\big]=\Phi\Big(\frac\mu\sigma\Big)+\exp\Big(\mu+\frac{\sigma^2}2\Big)\,\Phi\Big(-\sigma-\frac\mu\sigma\Big). $$
--
--   This computes the expected acceptance probability when the log acceptance ratio is Gaussian; it yields the speed $h(l)$ and the acceptance rate $a(l)$.
--
--   **Formalization Note** The paper writes $A\sim N(\mu,\sigma^2)$ and divides by $\sigma$; the formula is read with $\sigma>0$ (for $\sigma<0$ the law is the same but the right side changes). The variance is `(σ ^ 2).toNNReal`. The integrand lies in $(0,1]$, so the integral is a genuine expectation.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 115, Proposition 2.4

import Definitions.Def_Roberts1997_RWM_Speed

open MeasureTheory ProbabilityTheory

namespace Roberts1997.RWM

/-- Proposition 2.4 (p. 115). If `A ~ N(μ, σ²)` with `σ > 0`, then
`𝔼[1 ∧ e^A] = Φ(μ/σ) + exp(μ + σ²/2) Φ(-σ - μ/σ)`. -/
theorem expect_min_one_exp_gaussian (μ σ : ℝ) (hσ : 0 < σ) :
    ∫ a, min 1 (Real.exp a) ∂(gaussianReal μ (σ ^ 2).toNNReal) =
      Phi (μ / σ) + Real.exp (μ + σ ^ 2 / 2) * Phi (-σ - μ / σ) := by sorry

end Roberts1997.RWM
