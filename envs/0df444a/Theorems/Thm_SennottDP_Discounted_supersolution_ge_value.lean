-- Prove2me | Theorems.Thm_SennottDP_Discounted_supersolution_ge_value
-- name    : SennottDP.Discounted.supersolution_ge_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:02:37.972331+00:00
-- url     : https://prove2.me/theorems/9bc3a4eb-9522-4936-8a33-0fd5ff7d1882
-- title:
--   Corollary 4.1.3 — a supersolution of the optimality inequality dominates $V_{f,\alpha} \ge V_\alpha$
-- statement:
--   Let $\Delta$ be a Markov decision chain, $\alpha \in (0,1)$ and $W : S \to [0,\infty]$ a nonnegative function satisfying
--   $$W(i) \ge \min_{a} \Big\{ C(i,a) + \alpha \sum_j P_{ij}(a) W(j) \Big\}, \qquad i \in S. \tag{4.6}$$
--   Let $f$ be a stationary policy that realizes the right side of (4.6), that is, for each state $i$, $f(i)$ is an action that achieves the minimum. Then
--   $$W \ge V_{f,\alpha} \ge V_\alpha.$$
--
--   This is the step that turns any solution of the discount optimality inequality into an upper bound on the value function, and it gives the minimality half of Theorem 4.1.4.
--
--   **Formalization Note** $W$ may take the value $+\infty$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 62, Corollary 4.1.3, (4.6)

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Corollary 4.1.3, p. 62: let `W : S → [0, ∞]` satisfy
`W(i) ≥ min_a { C(i,a) + α ∑_j P_{ij}(a) W(j) }` for all `i` (4.6), and let `f` be a
stationary policy realizing the right side of (4.6). Then `W ≥ V_{f,α} ≥ V_α`. -/
theorem supersolution_ge_value {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (W : S → ℝ≥0∞)
    (hW : ∀ i, bellman M α W i ≤ W i) (f : StationaryPolicy M) (hf : Realizes M f α W) :
    ∀ i : S, discountedCost M f.toPolicy α i ≤ W i ∧
      valueFn M α i ≤ discountedCost M f.toPolicy α i := by sorry

end SennottDP.Discounted
