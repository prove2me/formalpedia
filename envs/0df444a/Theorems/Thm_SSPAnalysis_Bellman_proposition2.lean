-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_proposition2
-- name    : SSPAnalysis.Bellman.proposition2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:11:25.114951+00:00
-- url     : https://prove2.me/theorems/c0777242-a201-467f-b0e8-1a0e651ae426
-- title:
--   Proposition 2 — Bellman fixed point, value iteration, and optimal proper policy
-- statement:
--   Under Assumptions 1 and 2, let $x_i^*$ be the infimum of $x_i(\pi)$ over **all** policies, including nonstationary ones. This vector is finite and lies in $X=\{x:x_1=0\}$. It is the unique fixed point of the Bellman operator $T$ within $X$. For every $x\in X$, value iteration converges to it:
--
--   $$T(x^*)=x^*,\qquad T^t(x)\longrightarrow x^*.$$
--
--   A stationary selector $\mu$ is optimal if and only if $T_\mu(x^*)=T(x^*)$. There exists at least one optimal proper stationary selector.
--
--   The proposition connects the unrestricted policy-cost infimum with Bellman's equation and with both value iteration and stationary decision rules.
--
--   **Formalization Note.** Policy costs and their infimum are extended real; the theorem concludes the existence of a real vector representing $x^*$ rather than applying a default-valued conversion. State $1$ is `0 : Fin n`. $T^0$ is the identity. Control spaces are compact metric carriers, transition rows are probability vectors, and optimality compares against every policy.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 586, Proposition 2(a)–(c) and Furthermore clause

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Proposition 2 (p. 586), all parts: the optimal cost is the unique
Bellman fixed point in X, value iteration converges to it, stationary
optimality has the Bellman criterion, and an optimal proper policy exists. -/
theorem proposition2 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    [∀ i, MetricSpace (U i)] (m : Model n U)
    (h1 : m.Assumption1) (h2 : m.Assumption2) :
    ∃ xs : Fin n → ℝ,
      (∀ i, (xs i : EReal) = m.optCost i) ∧
      xs ∈ X n ∧
      m.T xs = xs ∧
      (∀ y ∈ X n, m.T y = y → y = xs) ∧
      (∀ x ∈ X n, Tendsto (fun t : ℕ => (m.T)^[t] x) atTop (𝓝 xs)) ∧
      (∀ μ : Selector U,
        m.IsOptimal (stationary μ) ↔ m.Tmu μ xs = m.T xs) ∧
      (∃ μ : Selector U, m.IsProper μ ∧ m.IsOptimal (stationary μ)) := by sorry

end SSPAnalysis.Bellman
