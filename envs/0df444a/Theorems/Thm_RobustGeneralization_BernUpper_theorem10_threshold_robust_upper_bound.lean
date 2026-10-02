-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_theorem10_threshold_robust_upper_bound
-- name    : RobustGeneralization.BernUpper.theorem10_threshold_robust_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:32:26.652071+00:00
-- url     : https://prove2.me/theorems/c6dfef9f-4902-4e09-8dce-e9582e71d7c3
-- title:
--   Theorem 10 — after thresholding, one Bernoulli sample gives ℓ∞^ε-robust error ≤ 1% for every ε < 1 when τ ≥ c·d^{−1/4}
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $d\in\mathbb N$, $\theta^\star\in\{\pm1\}^d$, and $0<\tau\le\tfrac12$ with
--   $$\tau\ \ge\ c\cdot d^{-1/4}.$$
--   Draw one sample $(x,y)$ from the $(\theta^\star,\tau)$-Bernoulli model and set $\hat w=yx$. Then, with probability at least $1-\exp(-\tau^2 d/2)$ over this sample, the classifier $f_{\hat w}\circ T$ satisfies, simultaneously for every $\varepsilon<1$,
--   $$\mathbb P_{(x',y')}\big[\exists\,x''\in\mathcal B^\varepsilon_\infty(x'):\ f_{\hat w}(T(x''))\neq y'\big]\ \le\ \frac1{100},$$
--   where $(x',y')$ is a fresh sample of the same model.
--
--   The result contrasts with the lower bound for linear classifiers in the same model (Theorem 9): a nonlinear classifier, the thresholding map followed by the linear classifier learned from one sample, is robust against every $\ell_\infty$ perturbation of size less than $1$ with the same sample complexity as standard generalization.
--
--   **Formalization Note.** "Universal constant" is an existential quantifier over $c>0$ placed before every other quantifier. "With high probability" is made explicit as the failure probability $\exp(-\tau^2d/2)$, the one the paper's Corollary 28 gives for the same classifier; under $\tau\ge c\,d^{-1/4}$ it is at most $\exp(-c^2\sqrt d/2)$. The statement bounds the probability of the failure event "some $\varepsilon<1$ has robust error above $1/100$", so one good event serves all $\varepsilon<1$ at once. Negative $\varepsilon$ is allowed as printed (the ball is then empty). $\tau\le\tfrac12$ is the standing restriction that makes the model a probability distribution. At $d=0$, Lean's $0^{-1/4}=0$ and the right side is $1$, so the statement is trivially true there.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 8, Theorem 10 (failure probability from p. 33, Corollary 28)

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 8, Theorem 10. There is a universal constant `c > 0`
such that for every `d`, every `θ⋆ = pm θ ∈ {±1}^d` and every `τ ∈ (0, 1/2]` with
`τ ≥ c · d^{−1/4}`: if `p = (x, y)` is one sample of the `(θ⋆, τ)`-Bernoulli model and
`ŵ = yx = zvec p`, then with probability at least `1 − exp(−τ²d/2)` over `p` the classifier
`f_ŵ ∘ T` has ℓ∞^ε-robust classification error at most `1/100` simultaneously for every
`ε < 1`; stated as a bound on the probability of the failure event. -/
theorem theorem10_threshold_robust_upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (θ : Fin d → Bool) (τ : ℝ), 0 < τ → τ ≤ 1 / 2 →
      c * (d : ℝ) ^ (-(1 : ℝ) / 4) ≤ τ →
      bprob θ τ (fun p => ∃ ε : ℝ, ε < 1 ∧ 1 / 100 < robErr θ τ (thrClf (zvec p)) ε)
        ≤ Real.exp (-(τ ^ 2 * d / 2)) := by sorry

end RobustGeneralization.BernUpper
