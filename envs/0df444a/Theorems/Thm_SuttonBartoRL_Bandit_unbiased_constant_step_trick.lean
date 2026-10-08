-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_unbiased_constant_step_trick
-- name    : SuttonBartoRL.Bandit.unbiased_constant_step_trick
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:49:09.263195+00:00
-- url     : https://prove2.me/theorems/093cb079-5122-4a85-a75c-6318f2dd8fef
-- title:
--   Exercise 2.7 — the unbiased constant-step-size trick removes the initial bias
-- statement:
--   Let $0 < \alpha \le 1$, let $\bar o_0 = 0$, $\bar o_n = \bar o_{n-1} + \alpha(1 - \bar o_{n-1})$ be the trace of one, and let $\beta_n = \alpha / \bar o_n$. Let $Q_1$ be arbitrary and let the estimates be updated with this step size:
--
--   $$
--   Q_{n+1} = Q_n + \beta_n\,[R_n - Q_n], \qquad n \ge 1.
--   $$
--
--   Then for every $n \ge 1$,
--
--   $$
--   Q_{n+1} = \sum_{i=1}^{n} \frac{\alpha (1-\alpha)^{n-i}}{\bar o_n}\, R_i,
--   \qquad
--   \sum_{i=1}^{n} \frac{\alpha (1-\alpha)^{n-i}}{\bar o_n} = 1 .
--   $$
--
--   That is, $Q_{n+1}$ is an exponential recency-weighted average of the rewards $R_1, \dots, R_n$ whose weights sum to one and in which the initial estimate $Q_1$ does not appear: the method has no initial bias.
--
--   **Formalization Note** The book asks to show that $Q_n$ is "an exponential recency-weighted average without initial bias" and gives no solution. The reading adopted here is: for every $n \ge 1$, $Q_{n+1}$ equals the displayed weighted average, with explicit weights proportional to $\alpha(1-\alpha)^{n-i}$ and summing to one, and hence independent of $Q_1$. The book calls $\alpha$ "a conventional constant step size"; the constant step size of (2.5) ranges over $(0, 1]$, and that range is assumed. (For $\alpha = 2$ the trace $\bar o_n$ vanishes at even $n$ and $\beta_n$ is undefined.)
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 2.7 with Eqs. (2.8)–(2.9), p. 35 (the book gives no solution)

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates

namespace SuttonBartoRL.Bandit

theorem unbiased_constant_step_trick (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Q R : ℕ → ℝ)
    (hQ : ∀ n : ℕ, 1 ≤ n → Q (n + 1) = Q n + unbiasedStepSize α n * (R n - Q n))
    (n : ℕ) (hn : 1 ≤ n) :
    Q (n + 1) = ∑ i ∈ Finset.Icc 1 n, (α * (1 - α) ^ (n - i) / traceOfOne α n) * R i ∧
      ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) / traceOfOne α n = 1 := by sorry

end SuttonBartoRL.Bandit
