-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_markov_policy_optimal
-- name    : SennottDP.FiniteHorizon.markov_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:28:35.604821+00:00
-- url     : https://prove2.me/theorems/8e20cfd8-f27d-49d5-8c15-318e5690213e
-- title:
--   Corollary 3.1.4 — choosing $f_{n-t}(i) \in B_i(\alpha, n-t)$ gives an optimal deterministic Markov policy
-- statement:
--   Let $\Delta$ be an MDC with countable state space, $F \ge 0$ a finite terminal cost, $0 < \alpha \le 1$ and $n \ge 1$. Let $f_1, \dots, f_n$ be stationary policies with
--   $$
--   f_{n-t}(i) \in B_i(\alpha, n-t) \qquad \text{for } 0 \le t \le n-1 \text{ and all } i \in S,
--   $$
--   and let $\theta = (f_n, f_{n-1}, \dots, f_1)$ be the deterministic Markov policy that uses $f_{n-t}$ at time $t$. Then $\theta$ is optimal for the $n$ horizon.
--
--   Together with the optimality equation this shows that an optimal policy for the $n$ horizon always exists and may be taken deterministic Markov, computed backward from $B_i(\alpha,1)$.
--
--   **Formalization Note** The sequence of stationary policies is indexed by $\mathbb N$; the policy used at time $t \ge n$ (the stationary policy $f_0$) plays no role in the $n$ horizon cost.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 40–41, Corollary 3.1.4

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Corollary 3.1.4 (Sennott, pp. 40–41). Let `n ≥ 1` and let `θ = (f_n, f_{n−1}, …, f_1)` be
the deterministic Markov policy that uses the stationary policy `f_{n−t}` at time `t`, where
`f_{n−t}(i) ∈ B_i(α, n − t)` for `0 ≤ t ≤ n − 1` and all `i`. Then `θ` is optimal for the
`n` horizon. (The stationary policy `f_0` used at times `t ≥ n` is irrelevant.) -/
theorem markov_policy_optimal {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : 1 ≤ n) (f : ℕ → M.Stationary)
    (hf : ∀ t, t ≤ n - 1 → ∀ i, (f (n - t)).1 i ∈ M.minSet F α (n - t) i) :
    M.IsOptimal F α n (MDC.Policy.ofMarkov (fun t => f (n - t))) := by sorry

end SennottDP.FiniteHorizon
