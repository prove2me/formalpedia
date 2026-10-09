-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_9
-- name    : PrimalDualPricing.Regret.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:06.821133+00:00
-- url     : https://prove2.me/theorems/49a8f24e-0977-4881-9de2-c3cdb3b484fe
-- title:
--   Lemma 9, p. 24 — Poisson deviation $\mathbb P(|N(r_n)-r_n|>r_n\epsilon_n)\le C/n^k$
-- statement:
--   Let $a,\beta,\gamma,\eta,q>0$. For a sequence $(r_n)_{n\ge1}$ with $r_n\ge a n^\beta$, set
--   $$\epsilon_n=\gamma(\log n)^{1/2+\eta}r_n^{-1/2},$$
--   and let $N(\mu)$ denote a Poisson random variable with mean $\mu$. Then there is a constant $C$, depending only on $a,\beta,\gamma,\eta,q$ and not on $n$ or on the sequence, such that
--   $$\mathbb P\big(|N(r_n)-r_n|>r_n\epsilon_n\big)\le\frac{C}{n^q}\qquad\text{for all }n\ge1.$$
--
--   The lemma controls every Poisson count of the algorithm at once. Its bound decays faster than any power of $n$, so a union bound over the polynomially many grid points and phases costs nothing.
--
--   **Formalization Note** The page's $\alpha$ and $k$ are renamed $a$ and $q$; they would clash with the algorithm's mark-up $\alpha$ and phase index $k$. The page leaves $\alpha,\gamma>0$ implicit; they are stated here. $C$ is chosen before the sequence $(r_n)$, as the page's "may depend on $\alpha,\beta,\gamma,\eta$ and $k$" says. The probability is under the Poisson law with mean $r_n$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 24, Appendix B, Lemma 9

import Mathlib

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 9 (Chen–Gallego, arXiv:1812.09234v3, p. 24). Let `a, β, γ, η, q > 0` (the page's `α, β, γ, η, k`,
renamed to avoid a clash with the algorithm's mark-up `α` and phase index `k`). There is a constant `C`,
depending only on `a, β, γ, η, q`, such that for every sequence `(r_n)` with `r_n ≥ a n^β` (`n ≥ 1`) and
`ε_n = γ (log n)^{1/2+η} r_n^{−1/2}`,
`P(|N(r_n) − r_n| > r_n ε_n) ≤ C / n^q` for all `n ≥ 1`, where `N(μ)` is Poisson with mean `μ`. -/
theorem lemma_9 (a β γ η q : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (hη : 0 < η)
    (hq : 0 < q) :
    ∃ C : ℝ, ∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → a * (n : ℝ) ^ β ≤ r n) →
      ∀ n : ℕ, 1 ≤ n →
        (poissonMeasure (r n).toNNReal
            {x : ℕ | r n * (γ * Real.log n ^ (1 / 2 + η) * r n ^ (-(1 / 2 : ℝ)))
              < |(x : ℝ) - r n|}).toReal
          ≤ C / (n : ℝ) ^ q := by sorry

end PrimalDualPricing.Regret
