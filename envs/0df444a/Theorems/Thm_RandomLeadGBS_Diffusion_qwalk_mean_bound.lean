-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_qwalk_mean_bound
-- name    : RandomLeadGBS.Diffusion.qwalk_mean_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:08.386992+00:00
-- url     : https://prove2.me/theorems/2fcbf2b8-a915-45e3-93a7-ce351ea3c1c8
-- title:
--   Proof of Lemma 4, p. 16, and EC.3 — the reflected walk Q_n has a unique stationary law with EQ ≤ [2(γ−1+δ)(γ−1)+γ²]/[2δ]
-- statement:
--   Let $\gamma\ge 1$ be an integer and $\epsilon>0$, and let $Q_n$ be the random walk on $\mathbb Z_+$ that moves from $q$ to $q+(\gamma-1)$ with probability $1/2+\epsilon$ and to $[q-\gamma]\vee 0$ with probability $1/2-\epsilon$. Put
--   $$
--   \delta = \Big(\tfrac12-\epsilon\Big)\gamma - \Big(\tfrac12+\epsilon\Big)(\gamma-1),
--   $$
--   so that $-\delta$ is the one-step drift when $Q_n\ge\gamma$, and assume $\delta>0$. Then $Q_n$ has exactly one stationary distribution, and for every stationary distribution the mean is finite with
--   $$
--   \mathbb E Q_\infty \le \frac{2(\gamma-1+\delta)(\gamma-1)+\gamma^2}{2\delta}.
--   $$
--   The walk dominates the gap $\tilde D^r$ at arrival epochs; this bound is what makes $\mathbb E\tilde D^r(\infty)$ bounded uniformly in large $r$ (Lemma 4).
--
--   **Formalization Note** The page calls $Q_n$ irreducible. For $\gamma=1$ the walk never leaves $0$, so irreducibility is not stated; the conclusion states existence and uniqueness of the stationary law, which holds for every $\gamma\ge 1$. Summability of $\sum_k p(k)\,k$ is part of the conclusion. Since $\delta>0$ forces $\epsilon<1/2$, both branch probabilities are positive.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 16 (proof of Lemma 4) and p. 44 (ec5), EC.3

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem qwalk_mean_bound (γ : ℕ) (hγ : 1 ≤ γ) (ε : ℝ) (hε : 0 < ε)
    (hδ : 0 < (1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1)) :
    (∃! p : ℕ → ℝ, IsDTMCStationary (qKernel γ ε) p) ∧
    ∀ p : ℕ → ℝ, IsDTMCStationary (qKernel γ ε) p →
      Summable (fun k : ℕ => p k * (k : ℝ)) ∧
      ∑' k : ℕ, p k * (k : ℝ) ≤
        (2 * ((γ : ℝ) - 1 + ((1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1))) * ((γ : ℝ) - 1)
            + (γ : ℝ) ^ 2) /
          (2 * ((1 / 2 - ε) * (γ : ℝ) - (1 / 2 + ε) * ((γ : ℝ) - 1))) := by sorry

end RandomLeadGBS.Diffusion
