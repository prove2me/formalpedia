-- Prove2me | Theorems.Thm_SennottDP_Discounted_value_function_min_solution_doe
-- name    : SennottDP.Discounted.value_function_min_solution_doe
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:05:44.901984+00:00
-- url     : https://prove2.me/theorems/fb320c74-3219-4f94-9ce2-a7b8babfa337
-- title:
--   Theorem 4.1.4 — $V_\alpha$ is the minimum nonnegative solution of the discount optimality equation
-- statement:
--   Let $\Delta$ be a Markov decision chain with countable state space $S$, finite nonempty action sets $A_i$, nonnegative costs $C(i,a)$ and transition probabilities $P_{ij}(a)$, and let $\alpha \in (0,1)$. Let $V_\alpha(i) = \inf_\theta V_{\theta,\alpha}(i)$ be the discounted value function, the infimum over all history-dependent randomized policies. Then:
--
--   1. $V_\alpha$ satisfies the discount optimality equation
--   $$V_\alpha(i) = \min_a \Big\{ C(i,a) + \alpha \sum_j P_{ij}(a) V_\alpha(j) \Big\}, \qquad i \in S; \tag{4.9}$$
--   2. $V_\alpha$ is the minimum nonnegative solution of (4.9): every $W : S \to [0,\infty]$ satisfying $W(i) = \min_a \{ C(i,a) + \alpha \sum_j P_{ij}(a) W(j) \}$ for all $i$ has $V_\alpha \le W$;
--   3. any stationary policy $f_\alpha$ that realizes the minimum in (4.9) is discount optimal: $V_{f_\alpha,\alpha}(i) = V_\alpha(i)$ for all $i \in S$.
--
--   This is the central result of the chapter: it characterizes the value function without any boundedness assumption on the costs and shows that an optimal policy can always be taken stationary and deterministic.
--
--   **Formalization Note** Values, including $V_\alpha$ and the competing solutions $W$, lie in $[0,\infty]$ and may be $+\infty$ (Remark 2.4.2); the equation holds in $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 63, Theorem 4.1.4, (4.9)

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Theorem 4.1.4, p. 63: the discounted value function `V_α` is the minimum
nonnegative solution of the discount optimality equation
`V_α(i) = min_a { C(i,a) + α ∑_j P_{ij}(a) V_α(j) }`, `i ∈ S` (4.9); that is, `V_α` solves
(4.9) and `V_α ≤ W` for every `W : S → [0, ∞]` solving (4.9). Any stationary policy `f_α`
that realizes the minimum in (4.9) is discount optimal. -/
theorem value_function_min_solution_doe {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ i : S, valueFn M α i = bellman M α (valueFn M α) i) ∧
      (∀ W : S → ℝ≥0∞, (∀ i, W i = bellman M α W i) → ∀ i, valueFn M α i ≤ W i) ∧
      (∀ f : StationaryPolicy M, Realizes M f α (valueFn M α) →
        IsDiscountOptimal M f.toPolicy α) := by sorry

end SennottDP.Discounted
