-- Prove2me | Theorems.Thm_RobustGeneralization_BernLower_eq5_posterior_odds_likelihood_ratio
-- name    : RobustGeneralization.BernLower.eq5_posterior_odds_likelihood_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:19:40.932962+00:00
-- url     : https://prove2.me/theorems/7bfc11cd-17aa-44b7-a0d6-92540532f95b
-- title:
--   Eqs. (4)–(5) — posterior odds of θ equal ∏ᵢ ((½+τ)/(½−τ))^{yᵢxᵢ}
-- statement:
--   Consider the one-dimensional Bernoulli model: $\theta$ is uniform on $\{-1,+1\}$ and, given $\theta$, the samples $(x_1,y_1),\dots,(x_n,y_n)\in\{\pm1\}^2$ are independent, each with $y_k$ uniform and $x_k=y_k\theta$ with probability $\tfrac12+\tau$, $x_k=-y_k\theta$ with probability $\tfrac12-\tau$. Let $0<\tau<\tfrac12$. Then for every sequence $S=((x_1,y_1),\dots,(x_n,y_n))$,
--   $$\frac{\Pr[\theta=+1\mid S]}{\Pr[\theta=-1\mid S]}=\prod_{k=1}^n\left(\frac{\tfrac12+\tau}{\tfrac12-\tau}\right)^{y_kx_k}.$$
--
--   This identity turns the posterior log-odds into a scaled sum $\log\frac{1/2+\tau}{1/2-\tau}\sum_k y_kx_k$ of independent $\pm1$ variables, which is what Lemma 29 bounds.
--
--   **Formalization Note** The posterior is defined by Bayes' rule as a ratio of joint weights, not as the likelihood product, so the statement is not a definitional unfolding. The exponent $y_kx_k\in\{\pm1\}$ is a real exponent of a positive base. $\tau<\tfrac12$ keeps every weight positive; the paper's section assumes $\tau\le\tfrac14$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 33, §B.2, proof of Lemma 29, eqs. (4)–(5)

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem eq5_posterior_odds_likelihood_ratio (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1 / 2)
    (S : Fin n → Bool × Bool) :
    odds1 τ S = ∏ k, ((1 / 2 + τ) / (1 / 2 - τ)) ^ (lab (S k).2 * lab (S k).1) := by sorry

end RobustGeneralization.BernLower
