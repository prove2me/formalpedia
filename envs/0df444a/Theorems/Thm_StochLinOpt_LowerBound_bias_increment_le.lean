-- Prove2me | Theorems.Thm_StochLinOpt_LowerBound_bias_increment_le
-- name    : StochLinOpt.LowerBound.bias_increment_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:35:21.815581+00:00
-- url     : https://prove2.me/theorems/54f0f381-7c60-4d95-b77d-f51f19ae35c5
-- title:
--   Section 6.1, Eq. (3) — the bias increment is at most $|(\mu_1-\mu_2)\cdot x|$
-- statement:
--   Let $\mu_1,\mu_2\in\mathbb R^2$ with $\|\mu_1\|=\|\mu_2\|=1/2$, let $x$ be a point of the unit circle, let $p\in[0,1]$ be the posterior probability of $\mu=\mu_1$, with bias $b=2p-1$, and let $\ell\in\{-1,+1\}$ be the observed cost. Let $b'$ be the Bayes-updated bias
--   $$b'=\frac{p(1+\ell\,\mu_1\cdot x)-(1-p)(1+\ell\,\mu_2\cdot x)}{p(1+\ell\,\mu_1\cdot x)+(1-p)(1+\ell\,\mu_2\cdot x)}.$$
--   Then
--   $$|b'-b|\le|(\mu_1-\mu_2)\cdot x|.$$
--
--   In Section 6.1 this is inequality (3): one observation moves the posterior bias by at most the difference of the two candidate expected costs of the decision. It is the only place where the size of the bias increment enters Lemma 15.
--
--   **Formalization Note** The paper writes the right side also as $\varepsilon|\alpha|$, where $\varepsilon=\|\mu_1-\mu_2\|$ and $\alpha$ is the coordinate of $x$ along $(\mu_1-\mu_2)/\varepsilon$; that equality is the definition of $\alpha$ and is not restated. The bias update is the Bayes rule (definition `biasUpdate`), not its simplified closed form. The statement allows every $p\in[0,1]$, while a genuine posterior lies in $(0,1)$; the inequality holds on the closed interval.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 11, Section 6.1, Eq. (3)

import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open Matrix

namespace StochLinOpt.LowerBound

theorem bias_increment_le (μ₁ μ₂ x : Fin 2 → ℝ) (p ℓ : ℝ)
    (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4) (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4) (hx : x ∈ unitCircle)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hℓ : ℓ = 1 ∨ ℓ = -1) :
    |biasUpdate μ₁ μ₂ x p ℓ - (2 * p - 1)| ≤ |(μ₁ - μ₂) ⬝ᵥ x| := by sorry

end StochLinOpt.LowerBound
