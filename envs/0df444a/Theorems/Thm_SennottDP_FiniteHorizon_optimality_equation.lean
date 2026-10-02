-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_optimality_equation
-- name    : SennottDP.FiniteHorizon.optimality_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:25:24.488307+00:00
-- url     : https://prove2.me/theorems/aa6b89e6-eb3b-4e62-ac63-512264175583
-- title:
--   Theorem 3.1.2 — the finite horizon optimality equation and the characterization of optimal policies
-- statement:
--   Let $\Delta$ be an MDC with countable state space, $F \ge 0$ a finite terminal cost, and $0 < \alpha \le 1$. The finite horizon value function satisfies the **finite horizon optimality equation**
--   $$
--   v_{\alpha,n}(i) = \min_{a \in A_i} \Big\{ C(i,a) + \alpha \sum_j P_{ij}(a)\, v_{\alpha,n-1}(j) \Big\}, \qquad i \in S,\ n \ge 1. \tag{3.2}
--   $$
--   Moreover, with $B_i(\alpha,n)$ the set of actions attaining this minimum:
--
--   1. A policy $\theta$ is optimal for the $1$ horizon if and only if, for every initial state $i$, the distribution $\theta(\cdot \mid i)$ is concentrated on $B_i(\alpha,1)$.
--   2. For $n \ge 2$, a policy $\theta$ is optimal for the $n$ horizon if and only if, for every initial state $i$: (1) $\theta(\cdot \mid i)$ is concentrated on $B_i(\alpha,n)$; and (2) if $v_{\alpha,n}(i) < \infty$, then for every action $a$ with $\theta(a \mid i) > 0$ and every state $j$ with $P_{ij}(a) > 0$, the continuation policy $\psi(i,a,j)$ that $\theta$ follows from $t = 1$ is optimal for the $n-1$ horizon at the initial state $j$: $v_{\psi(i,a,j),\alpha,n-1}(j) = v_{\alpha,n-1}(j)$.
--
--   Policies here are general: history dependent and randomized. The theorem gives both the recursion that computes $v_{\alpha,n}$ and Bellman's principle of optimality in necessary-and-sufficient form.
--
--   **Formalization Note** The book states (2) without the clause "if $v_{\alpha,n}(i) < \infty$". That clause is needed for the "only if" direction: when $v_{\alpha,n}(i) = \infty$, every policy attains $v_{\alpha,n}(i)$, including one that acts suboptimally after reaching a state $j$ with $v_{\alpha,n-1}(j) < \infty$. The book's proof of necessity uses a strict inequality that holds only when $v_{\alpha,n}(i)$ is finite. "Given the process moves to state $j$ at $t = 1$" is read as: the pair $(a,j)$ is reachable, $\theta(a \mid i) > 0$ and $P_{ij}(a) > 0$. The continuation policy is `θ.shift i a`, and `θ.σ [] i a` is $\theta(a \mid i)$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 36–37, Theorem 3.1.2 (Eq. (3.2)); proof pp. 37–39

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Theorem 3.1.2 (Sennott, pp. 36–37), with a correction to the necessity of (ii)(2).
Let `0 < α ≤ 1` and a nonnegative terminal cost `F`. The finite horizon value function satisfies
the finite horizon optimality equation (3.2)
`v_{α,n}(i) = min_{a ∈ A_i} {C(i,a) + α ∑_j P_ij(a) v_{α,n−1}(j)}`, `i ∈ S`, `n ≥ 1`, and:
(i) a (general) policy `θ` is optimal for the 1 horizon iff for every initial state `i` the
distribution `θ(· | i)` is concentrated on `B_i(α, 1)`;
(ii) for `n ≥ 2`, `θ` is optimal for the `n` horizon iff for every initial state `i`:
(1) `θ(· | i)` is concentrated on `B_i(α, n)`, and (2) whenever `v_{α,n}(i) < ∞`, for every
action `a` with `θ(a | i) > 0` and every state `j` with `P_ij(a) > 0`, the continuation policy
`ψ(i, a, j)` of `θ` is optimal for the `n − 1` horizon at `j`.
The guard `v_{α,n}(i) < ∞` in (2) is not in the book; without it the "only if" fails when
`v_{α,n}(i) = ∞` (then every policy is optimal at `i`). -/
theorem optimality_equation {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∀ n, 1 ≤ n → ∀ i, M.value F α n i = (M.A i).inf' (M.A_nonempty i) (M.aux F α n i)) ∧
    (∀ θ : M.Policy, M.IsOptimal F α 1 θ ↔
      ∀ i a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α 1 i) ∧
    (∀ n, 2 ≤ n → ∀ θ : M.Policy, M.IsOptimal F α n θ ↔
      ∀ i, (∀ a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α n i) ∧
        (M.value F α n i < ⊤ → ∀ a j, θ.σ [] i a ≠ 0 → M.P i a j ≠ 0 →
          MDC.horizonCost F α (θ.shift i a) (n - 1) j = M.value F α (n - 1) j)) := by sorry

end SennottDP.FiniteHorizon
