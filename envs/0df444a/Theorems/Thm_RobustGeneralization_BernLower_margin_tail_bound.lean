-- Prove2me | Theorems.Thm_RobustGeneralization_BernLower_margin_tail_bound
-- name    : RobustGeneralization.BernLower.margin_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:22:10.123359+00:00
-- url     : https://prove2.me/theorems/6f2bc092-a48e-40e6-807b-ea491b381906
-- title:
--   Proof of Thm 31 (p. 37) — margin tail: w.p. ≥ (1 − γ)/2, ⟨w, yx⟩ ≤ (a_n/γ)‖w‖₁
-- statement:
--   Let $0<\tau\le\tfrac12$, $0\le b\le1$ and $\gamma>0$. Let $m\in\mathbb R^d$ with $|m_i|\le b$ for all $i$, and let $\theta^\star$ follow the product law $\rho_m$ on $\{\pm1\}^d$ with independent coordinates of means $\mathbb E[\theta^\star_i]=m_i$. Given $\theta^\star$, let $(x,y)$ be a fresh sample from the $(\theta^\star,\tau)$-Bernoulli model. Then for every $w\in\mathbb R^d$, with $a=2\tau b$,
--   $$\Pr_{\theta^\star\sim\rho_m,\ (x,y)}\Big[\langle w,yx\rangle\le\frac{a}{\gamma}\|w\|_1\Big]\ge\frac{1-\gamma}{2}.$$
--
--   In the proof of Theorem 31 this is applied conditionally on the sample set $S$: given $S$, the posterior of $\theta^\star$ is a product law whose coordinate means satisfy $|\mathbb E[\theta^\star_i\mid S]|\le b=15\tau\sqrt{2n\log(4d/\gamma)}$, so $a=a_n=30\tau^2\sqrt{2n\log(4d/\gamma)}$ is the page's shorthand. The statement here is the general product-law form that the argument uses.
--
--   **Formalization Note** The probability is the finite sum $\sum_\theta\rho_m(\theta)\sum_{(x,y)}P_{\theta,\tau}(x,y)\,\mathbf 1[\cdot]$. $\|w\|_1=\sum_i|w_i|$. The bound $b\le1$ (with $\tau\le\tfrac12$) makes $\rho_m$ a probability law and $a\le1$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 37, §B.2, proof of Theorem 31, from 'To simplify the following calculation' to '⟨w, yx⟩ ≤ (a_n/γ)‖w‖₁'

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem margin_tail_bound (d : ℕ) (τ b γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (m : Fin d → ℝ) (hm : ∀ i, |m i| ≤ b) (w : E d) (hγ : 0 < γ) :
    (1 - γ) / 2 ≤ ∑ θ : Fin d → Bool, prodLaw m θ * ∑ p : (Fin d → Bool) × Bool,
      bernW θ τ p *
        (if lab p.2 * inner ℝ w (pm p.1) ≤ (2 * τ * b / γ) * ∑ i, |w i| then 1 else 0) := by sorry

end RobustGeneralization.BernLower
