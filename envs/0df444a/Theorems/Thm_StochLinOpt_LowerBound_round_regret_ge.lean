-- Prove2me | Theorems.Thm_StochLinOpt_LowerBound_round_regret_ge
-- name    : StochLinOpt.LowerBound.round_regret_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:35:58.404221+00:00
-- url     : https://prove2.me/theorems/84bad66d-724f-47e7-9de5-d6ad3829ba5f
-- title:
--   Lemma 15 — per-round Bayesian regret $\ge\frac1{16}(\varepsilon^2+|b_{t+1}-b_t|^2/\varepsilon^2)\,\mathbf 1\{|b_t|\le1/2\}$
-- statement:
--   Let $\mu_1,\mu_2\in\mathbb R^2$ with $\|\mu_1\|=\|\mu_2\|=1/2$ and $\|\mu_1-\mu_2\|=\varepsilon>0$. Suppose that, given the history $\mathcal H_t$ before round $t$, the mean is $\mu_1$ with probability $p\in[0,1]$ and $\mu_2$ with probability $1-p$, so the bias is $b_t=2p-1$. Let the decision on round $t$ be a point $x$ of the unit circle, let $\ell\in\{-1,+1\}$ be the cost observed on round $t$, and let $b_{t+1}$ be the Bayes-updated bias (as in Eq. (3)). The expected regret of round $t$ given $\mathcal H_t$ is
--   $$\mathbb E_\mu(r_t\mid\mathcal H_t)=p\,(\mu_1\cdot x-\mu_1\cdot x^*_1)+(1-p)\,(\mu_2\cdot x-\mu_2\cdot x^*_2),$$
--   where $\mu_i\cdot x^*_i=\min_{y\in S^1}\mu_i\cdot y$. Then, for either value of $\ell$,
--   $$\mathbb E_\mu(r_t\mid\mathcal H_t)\ \ge\ \frac1{16}\Big(\varepsilon^2+\frac{|b_{t+1}-b_t|^2}{\varepsilon^2}\Big)\,\mathbf 1\{|b_t|\le1/2\}.$$
--
--   This is the per-round trade-off behind the $\Omega(\sqrt T)$ lower bound: while the posterior is undecided, every round either costs regret of order $\varepsilon^2$ or, through a large movement of the bias, costs regret of order $|b_{t+1}-b_t|^2/\varepsilon^2$.
--
--   **Formalization Note** The history $\mathcal H_t$ enters only through the posterior probability $p$ and the decision $x$, so the lemma is stated for arbitrary $p\in[0,1]$ and arbitrary $x$ on the circle; a genuine posterior lies in $(0,1)$. The right side depends on $\ell_t$, which is not part of $\mathcal H_t$; the paper's "for any sequence of decisions $x_1,\dots,x_t$ and outcomes $\ell_1,\dots,\ell_{t-1}$" is read as "for either value of $\ell_t$", which is what the paper's proof establishes (via Eq. (3)). The distance $\varepsilon$ is pinned by $\varepsilon>0$ and $(\mu_1-\mu_2)\cdot(\mu_1-\mu_2)=\varepsilon^2$ (the Euclidean norm, not Lean's sup norm on `Fin 2 → ℝ`). The indicator is written as an `if`.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 11, Lemma 15

import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open Matrix

namespace StochLinOpt.LowerBound

theorem round_regret_ge (μ₁ μ₂ x : Fin 2 → ℝ) (ε p ℓ : ℝ)
    (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4) (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4)
    (hε : 0 < ε) (hdist : (μ₁ - μ₂) ⬝ᵥ (μ₁ - μ₂) = ε ^ 2) (hx : x ∈ unitCircle)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hℓ : ℓ = 1 ∨ ℓ = -1) :
    1 / 16 * (ε ^ 2 + (biasUpdate μ₁ μ₂ x p ℓ - (2 * p - 1)) ^ 2 / ε ^ 2) *
        (if |2 * p - 1| ≤ 1 / 2 then 1 else 0) ≤
      p * (μ₁ ⬝ᵥ x - optCost μ₁) + (1 - p) * (μ₂ ⬝ᵥ x - optCost μ₂) := by sorry

end StochLinOpt.LowerBound
