-- Prove2me | Theorems.Thm_RobustGeneralization_BernLower_posterior_mean_bound
-- name    : RobustGeneralization.BernLower.posterior_mean_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:20:47.132705+00:00
-- url     : https://prove2.me/theorems/6ef3a532-00e6-44a6-8269-3e4476931b5a
-- title:
--   Proof of Thm 31 (p. 36) — w.p. 1 − γ/2, |E[θ⋆ᵢ|S]| ≤ 15τ√(2n log(4d/γ)) for all i
-- statement:
--   Let $\theta^\star$ be uniform on $\{\pm1\}^d$ and let $S$ be $n$ independent samples from the $(\theta^\star,\tau)$-Bernoulli model. Write $\mathbb E[\theta^\star_i\mid S]=\Pr[\theta^\star_i=+1\mid S]-\Pr[\theta^\star_i=-1\mid S]$ for the posterior mean of the $i$-th coordinate. Assume $0<\tau\le\tfrac14$, $n\le1/\tau^2$, $\gamma>0$, and
--   $$b_n:=15\tau\sqrt{2n\log\tfrac{4d}{\gamma}}\le1.$$
--   Then, with probability at least $1-\gamma/2$ over $(\theta^\star,S)$,
--   $$\big|\mathbb E[\theta^\star_i\mid S]\big|\le 15\tau\sqrt{2n\log\tfrac{4d}{\gamma}}\qquad\text{for all } i\in[d].$$
--
--   This is the step of the proof of Theorem 31 where the learner's uncertainty about every bit of $\theta^\star$ is made quantitative; it combines Lemma 29 (with $\delta=\gamma/(2d)$) over the $d$ coordinates.
--
--   **Formalization Note** The hypothesis $b_n\le1$ is the page's remark that "the argument to the exponential function is in this range", which the sample bound of Theorem 31 implies; it is kept explicit here. The probability is the finite sum of joint weights $2^{-d}\prod_k P_{\theta,\tau}(x_k,y_k)$ over $\theta$ and $S$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 36, §B.2, proof of Theorem 31, the displays from 'Next, we bound the ratio of probabilities' to '|E[θ⋆_i|S]| ≤ 15τ√(2n log(4d/γ))'

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem posterior_mean_bound (d n : ℕ) (τ γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (hn : (n : ℝ) ≤ 1 / τ ^ 2) (hγ : 0 < γ)
    (hx : 15 * τ * Real.sqrt (2 * n * Real.log (4 * d / γ)) ≤ 1) :
    1 - γ / 2 ≤ ∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool,
      joint τ θ S *
        (if ∀ i, |postMean τ S i| ≤ 15 * τ * Real.sqrt (2 * n * Real.log (4 * d / γ))
          then 1 else 0) := by sorry

end RobustGeneralization.BernLower
