-- Prove2me | Theorems.Thm_SuttonBartoRL_ImportanceSampling_weighted_average_incremental
-- name    : SuttonBartoRL.ImportanceSampling.weighted_average_incremental
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:32:48.930147+00:00
-- url     : https://prove2.me/theorems/603335db-ba36-4307-a85a-9553346fb493
-- title:
--   The incremental rule (5.8) computes the weighted average (5.7)
-- statement:
--   Let $G_1, G_2, \dots$ be returns and $W_1, W_2, \dots$ nonnegative weights with $W_1 > 0$. Let $C_0 = 0$, $C_{n+1} = C_n + W_{n+1}$, let $V_1$ be arbitrary, and let
--
--   $$
--   V_{n+1} = V_n + \frac{W_n}{C_n}\bigl[G_n - V_n\bigr], \qquad n \ge 1 .
--   $$
--
--   Then for every $n \ge 2$,
--
--   $$
--   V_n = \frac{\sum_{k=1}^{n-1} W_k G_k}{\sum_{k=1}^{n-1} W_k} .
--   $$
--
--   This is Exercise 5.10 ("Derive the weighted-average update rule (5.8) from (5.7)"): the incremental update is an exact implementation of weighted importance sampling.
--
--   **Formalization Note** The hypotheses $W_k \ge 0$ (weights are importance-sampling ratios) and $W_1 > 0$ are added. Without $W_1 > 0$ the claim fails: if $W_1 = 0$ then $C_1 = 0$, the update (5.8) at $n = 1$ divides by zero, and $V_2$ need not equal the weighted average (5.7) at $n = 2$, whose denominator is also zero.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.6, Eqs. (5.7)–(5.8), p. 109; Exercise 5.10, p. 109

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_WeightedAverage

namespace SuttonBartoRL.ImportanceSampling

/-- Sutton & Barto (2018), §5.6, p. 109, Exercise 5.10 (the book gives no solution): the
incremental rule (5.8) with `C_0 = 0`, `C_{n+1} = C_n + W_{n+1}` and arbitrary `V_1` computes the
weighted average (5.7), `V_n = Σ_{k=1}^{n-1} W_k G_k / Σ_{k=1}^{n-1} W_k` for every `n ≥ 2`, provided
the weights are nonnegative and `W_1 > 0` (so that no `C_n`, `n ≥ 1`, is zero). -/
theorem weighted_average_incremental (W G : ℕ → ℝ) (V₁ : ℝ) (hW : ∀ k, 1 ≤ k → 0 ≤ W k)
    (hW1 : 0 < W 1) (n : ℕ) (hn : 2 ≤ n) :
    incrementalEstimate W G V₁ n = weightedAverage W G n := by sorry

end SuttonBartoRL.ImportanceSampling
