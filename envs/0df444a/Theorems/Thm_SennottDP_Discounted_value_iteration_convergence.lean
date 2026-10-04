-- Prove2me | Theorems.Thm_SennottDP_Discounted_value_iteration_convergence
-- name    : SennottDP.Discounted.value_iteration_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:18:55.004072+00:00
-- url     : https://prove2.me/theorems/198b84fd-4ca2-42bd-a31a-f6b4e26cf249
-- title:
--   Proposition 4.3.1 — $v_{\alpha,n} \uparrow V_\alpha$ and limit points of finite horizon optimal policies are discount optimal
-- statement:
--   Let $\Delta$ be a Markov decision chain and $\alpha \in (0,1)$, and let $v_{\alpha,n}$ be the $n$-horizon expected discounted value function with terminal cost zero. Then $v_{\alpha,n}(i)$ is increasing in $n$ and
--   $$\lim_{n \to \infty} v_{\alpha,n}(i) = V_\alpha(i), \qquad i \in S.$$
--   Moreover, suppose that for each $n \ge 1$, $f_{\alpha,n}$ is a stationary policy realizing the minimum in the finite horizon optimality equation
--   $$v_{\alpha,n}(i) = \min_a \Big\{ C(i,a) + \alpha \sum_j P_{ij}(a) v_{\alpha,n-1}(j) \Big\}, \qquad i \in S. \tag{3.2}$$
--   Then any limit point of the sequence $(f_{\alpha,n})_{n \ge 1}$ is discount optimal for the infinite horizon.
--
--   This justifies value iteration started from zero for the discounted criterion with unbounded costs.
--
--   **Formalization Note** The sequence is indexed by all $n \in \mathbb N$; its $0$-th entry is unconstrained and cannot affect limit points. "Realizing the minimum in (3.2)" is stated for the right side of (3.2) with $v_{\alpha,n-1}$; the book proves in Chapter 3 that this right side equals $v_{\alpha,n}$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 66, Proposition 4.3.1; (3.2) p. 37; Definition B.1 pp. 288–289

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Proposition 4.3.1, p. 66: with terminal cost zero, the finite horizon value
function `v_{α,n}` is increasing in `n` and `lim_{n→∞} v_{α,n} = V_α`. If, for each `n ≥ 1`,
`f_{α,n}` is a stationary policy realizing the minimum in the finite horizon optimality equation
(3.2), `v_{α,n}(i) = min_a { C(i,a) + α ∑_j P_{ij}(a) v_{α,n-1}(j) }`, then every limit point
(Definition B.1) of the sequence `(f_{α,n})_{n ≥ 1}` is discount optimal for the infinite horizon.
The entry `fs 0` of the sequence is unconstrained and does not affect limit points. -/
theorem value_iteration_convergence {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ i : S, Monotone (fun n : ℕ => finiteValueFn M α n i) ∧
        Tendsto (fun n : ℕ => finiteValueFn M α n i) atTop (𝓝 (valueFn M α i))) ∧
      ∀ fs : ℕ → StationaryPolicy M,
        (∀ n : ℕ, 1 ≤ n → Realizes M (fs n) α (finiteValueFn M α (n - 1))) →
        ∀ f : StationaryPolicy M, IsLimitPoint M fs f →
          IsDiscountOptimal M f.toPolicy α := by sorry

end SennottDP.Discounted
