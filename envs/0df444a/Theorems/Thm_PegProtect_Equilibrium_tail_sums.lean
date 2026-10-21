-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_tail_sums
-- name    : PegProtect.Equilibrium.tail_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:21.625493+00:00
-- url     : https://prove2.me/theorems/f3f08f1c-5b45-4c01-8ec0-67f922a918ba
-- title:
--   Proof of Proposition 3.1, p. 35, and p. 16 — Σ_k q_k = 1, Σ_{k≥0} q_k = 1/(1+ω), Σ_{k<0} q_k = ω/(1+ω)
-- statement:
--   Let $0\le\omega<1$ and let $q_k=\frac{1-\omega}{1+\omega}\omega^{|k|}$ ($k\in\mathbb Z$) be the discrete Laplace law. Then $q$ sums to one, and its two tails have the masses
--   $$\sum_{k\in\mathbb Z}q_k=1,\qquad \sum_{k=0}^{\infty}q_k=\frac{1}{1+\omega},\qquad \sum_{k=-\infty}^{-1}q_k=\frac{\omega}{1+\omega}.$$
--
--   The first identity completes the proof that $q$ is a probability distribution; the other two are the probabilities that an arriving investor finds no, respectively some, contra-side liquidity at the midpoint, and they enter every payoff of the model.
--
--   **Formalization Note** The paper's Proposition 3.1 takes $\omega\in(0,1)$; the statement includes $\omega=0$, where $q$ is the point mass at $0$, because Definition 3.1's corner case evaluates the payoffs there. The one-sided sums are over $k=n$ and $k=-(n+1)$, $n\in\mathbb N$.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 35, proof of Proposition 3.1 (Σ_{k∈Z} q_k = 1), and p. 16, §3.4 (Σ_{k=0}^∞ q_k = 1/(1+ω))

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem tail_sums (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω < 1) :
    HasSum (q ω) 1 ∧
    ∑' n : ℕ, q ω n = 1 / (1 + ω) ∧
    ∑' n : ℕ, q ω (-((n : ℤ) + 1)) = ω / (1 + ω) := by sorry

end PegProtect.Equilibrium
