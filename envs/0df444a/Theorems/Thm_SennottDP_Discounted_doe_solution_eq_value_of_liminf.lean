-- Prove2me | Theorems.Thm_SennottDP_Discounted_doe_solution_eq_value_of_liminf
-- name    : SennottDP.Discounted.doe_solution_eq_value_of_liminf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:11:20.905015+00:00
-- url     : https://prove2.me/theorems/2c683c9d-2eee-4797-8fed-528b1ead3ee2
-- title:
--   Proposition 4.2.2 — a solution of (4.9) with vanishing discounted tail equals $V_\alpha$
-- statement:
--   Let $\Delta$ be a Markov decision chain and $\alpha \in (0,1)$. Let $W : S \to [0,\infty]$ be a nonnegative solution of the discount optimality equation (4.9), and let $f_\alpha$ be an optimal stationary policy as in Theorem 4.1.4, that is, a stationary policy realizing the minimum in (4.9) for $V_\alpha$. If
--   $$\liminf_{n \to \infty} \alpha^n E_{f_\alpha}[W(X_n) \mid X_0 = i] = 0, \qquad i \in S, \tag{4.15}$$
--   then $W = V_\alpha$.
--
--   Since (4.9) in general has many solutions (Example 4.2.1 of the book), this gives a checkable condition under which a solution is the value function.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 65, Proposition 4.2.2, (4.15)

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Proposition 4.2.2, p. 65: let `W : S → [0, ∞]` be a solution of the discount
optimality equation (4.9) and let `f_α` be an optimal stationary policy as in Theorem 4.1.4
(one realizing the minimum in (4.9)). If
`liminf_{n→∞} α^n E_{f_α}[W(X_n) | X_0 = i] = 0` for every `i ∈ S` (4.15), then `W = V_α`. -/
theorem doe_solution_eq_value_of_liminf {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (W : S → ℝ≥0∞)
    (hW : ∀ i, W i = bellman M α W i) (f : StationaryPolicy M)
    (hf : Realizes M f α (valueFn M α))
    (hlim : ∀ i : S,
      liminf (fun n : ℕ => (α : ℝ≥0∞) ^ n * expState M f.toPolicy i n W) atTop = 0) :
    W = valueFn M α := by sorry

end SennottDP.Discounted
