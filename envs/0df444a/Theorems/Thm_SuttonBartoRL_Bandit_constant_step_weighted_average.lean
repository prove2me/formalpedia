-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_constant_step_weighted_average
-- name    : SuttonBartoRL.Bandit.constant_step_weighted_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:03.980978+00:00
-- url     : https://prove2.me/theorems/deec2e25-3f27-4bd4-9fe3-38ca02aa02a1
-- title:
--   Eq. (2.6) — constant step size gives an exponential recency-weighted average
-- statement:
--   Let $\alpha \in (0, 1]$ be a constant step size, $R_1, R_2, \dots$ real rewards and $Q_1$ an initial estimate, and let the estimates be updated by
--
--   $$
--   Q_{n+1} = Q_n + \alpha\,[R_n - Q_n], \qquad n \ge 1. \qquad (2.5)
--   $$
--
--   Then for every $n$,
--
--   $$
--   Q_{n+1} = (1-\alpha)^n Q_1 + \sum_{i=1}^{n} \alpha (1-\alpha)^{n-i} R_i,
--   \qquad
--   (1-\alpha)^n + \sum_{i=1}^{n} \alpha (1-\alpha)^{n-i} = 1 .
--   $$
--
--   So $Q_{n+1}$ is a weighted average of the initial estimate and past rewards, with weights decaying geometrically in the age $n-i$ of a reward; the initial estimate keeps weight $(1-\alpha)^n$, which is the initial bias of constant step sizes.
--
--   **Formalization Note** The book's convention $0^0 = 1$ (p. 33) is Lean's, so $\alpha = 1$ is covered. The statement also holds trivially at $n = 0$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (2.5)–(2.6), p. 32, and the weight-sum identity, p. 33

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates

namespace SuttonBartoRL.Bandit

theorem constant_step_weighted_average (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Q R : ℕ → ℝ)
    (hQ : ∀ n : ℕ, 1 ≤ n → Q (n + 1) = Q n + α * (R n - Q n)) (n : ℕ) :
    Q (n + 1) = (1 - α) ^ n * Q 1 + ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) * R i ∧
      (1 - α) ^ n + ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) = 1 := by sorry

end SuttonBartoRL.Bandit
