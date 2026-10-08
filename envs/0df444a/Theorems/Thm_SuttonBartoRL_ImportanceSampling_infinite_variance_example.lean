-- Prove2me | Theorems.Thm_SuttonBartoRL_ImportanceSampling_infinite_variance_example
-- name    : SuttonBartoRL.ImportanceSampling.infinite_variance_example
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:52:59.56905+00:00
-- url     : https://prove2.me/theorems/43749738-b98e-41bc-9294-83b6a7ff1b2f
-- title:
--   Example 5.5: ordinary importance sampling with infinite variance
-- statement:
--   In the one-state MDP of Example 5.5 (from $s$, **right** terminates with reward $0$; **left** returns to $s$ with probability $0.9$ and reward $0$ or terminates with probability $0.1$ and reward $+1$), take $\gamma = 1$, the target policy $\pi$ that always selects left and the behaviour policy $b$ that selects left and right with probability $\tfrac12$ each. Then:
--
--   1. the value of $s$ under the target policy is $v_\pi(s) = 1$;
--   2. the importance-sampling-scaled return has mean one, $\mathbb E_b[\rho_{0:T-1} G_0 \mid S_0 = s] = 1$;
--   3. its expected square is infinite:
--   $$
--   \mathbb E_b\Bigl[\Bigl(\prod_{t=0}^{T-1} \frac{\pi(A_t \mid S_t)}{b(A_t \mid S_t)}\, G_0\Bigr)^2\Bigr] = 0.1 \sum_{k=0}^{\infty} 0.9^k \cdot 2^k \cdot 2 = \infty .
--   $$
--
--   Hence the ordinary importance-sampling estimator has infinite variance in this example, although its mean is finite and correct.
--
--   **Formalization Note** Episodes here have unbounded length. The expectations are series over episode lengths; the expected square is computed in $[0, \infty]$ (`ℝ≥0∞`), where a divergent series has the value $+\infty$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Example 5.5 'Infinite Variance', pp. 106–108, Figure 5.4

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes
import Definitions.Def_SuttonBartoRL_ImportanceSampling_InfiniteVarianceExample

namespace SuttonBartoRL.ImportanceSampling

/-- Sutton & Barto (2018), Example 5.5 "Infinite Variance", pp. 106–108 (Figure 5.4), with `γ = 1`:
the value of `s` under the target policy (always `left`) is `1`; the importance-sampling-scaled
return `ρ_{0:T-1} G_0` of an episode from `s` under the behaviour policy (`left`/`right` with
probability `1/2`) has mean `1`; and its expected square is `+∞`. -/
theorem infinite_variance_example :
    value exampleMDP exampleTerminal exampleTarget 1 ExState.s = 1 ∧
    expectation exampleMDP exampleTerminal exampleBehavior ExState.s
      (fun n e => e.isRatio exampleTarget exampleBehavior n * e.ret 1) = 1 ∧
    ∑' n : ℕ, ∑ e : Episode exampleMDP n,
      ENNReal.ofReal (episodeProb exampleMDP exampleTerminal exampleBehavior ExState.s e *
        (e.isRatio exampleTarget exampleBehavior n * e.ret 1) ^ 2) = ⊤ := by sorry

end SuttonBartoRL.ImportanceSampling
