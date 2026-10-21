-- Prove2me | Theorems.Thm_SurgeAppt_FirstAvail_eq_11_bellman
-- name    : SurgeAppt.FirstAvail.eq_11_bellman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:43.467903+00:00
-- url     : https://prove2.me/theorems/d1b9cdcd-c10b-4d3f-ab91-b20ad87f87b2
-- title:
--   (11), p. 10 — $V^*$ solves the Bellman equation and a stationary policy minimizing its right-hand side is optimal
-- statement:
--   In the appointment-scheduling model of §3 under its standing assumptions, let $V^*(\mathbf S) = \inf_\pi V_\pi(\mathbf S)$ be the optimal value function (10), the infimum running over admissible (Markov deterministic) policies. For a function $V$ on books write
--
--   $$
--   Q_V(\mathbf S, a, \mathbf u) = g(\mathbf S, a, \mathbf u) + \beta\sum_{\mathbf S'}\mathbb P(\mathbf S'\mid\mathbf S+\mathbf u)\,V(\mathbf S').
--   $$
--
--   There is a stationary admissible decision rule $\sigma$ such that
--
--   1. $\sigma(\mathbf S, a)$ minimizes $Q_{V^*}(\mathbf S, a, \cdot)$ over the admissible actions (1), for every valid $\mathbf S$ and every $a\le M$;
--   2. $V^*$ solves the Bellman equation (11): for every valid $\mathbf S$,
--   $$
--   V^*(\mathbf S) = \sum_{a=0}^M \mathbb P(A=a)\,\min_{\mathbf u\in\mathcal U(\mathbf S,a)} Q_{V^*}(\mathbf S,a,\mathbf u);
--   $$
--   3. $\sigma$ is optimal: $V_\sigma(\mathbf S) = V^*(\mathbf S)$, and $V_\sigma(\mathbf S)\le V_\pi(\mathbf S)$ for every admissible policy $\pi$ and every valid $\mathbf S$.
--
--   **Formalization Note** The minimum over $\mathcal U$ in (11) is written through the minimizer $\sigma$ (item 1), with the arrival $a$ realized before the decision, as in the LP of p. 11. Item 3 states optimality both as $V_\sigma = V^*$ and directly against every admissible policy, so that nothing rests on the real infimum.
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), p. 10, (10)–(11)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

namespace SurgeAppt.FirstAvail

/-- (11), p. 10: the optimal value function `V*` of (10) solves the Bellman equation
`V*(S) = ∑_a P(A = a) min_{u ∈ (1)} (g(S, u) + β ∑_{S'} P(S' | S + u) V*(S'))` at every valid state,
and a stationary policy `σ` that minimizes the right-hand side exists and is optimal. -/
theorem eq_11_bellman (P : Params) (hP : P.Standing) :
    ∃ σ : Book P → ℕ → Book P, IsAdmissible P (fun _ => σ) ∧
      (∀ s, Valid P s → ∀ a, a ≤ P.M → ∀ u, Admissible P s a u →
        qValue P (optValue P) s a (σ s a) ≤ qValue P (optValue P) s a u) ∧
      (∀ s, Valid P s →
        optValue P s = ∑ a ∈ Finset.range (P.M + 1), P.pA a * qValue P (optValue P) s a (σ s a)) ∧
      (∀ s, Valid P s → value P (fun _ => σ) s = optValue P s) ∧
      (∀ π : Policy P, IsAdmissible P π → ∀ s, Valid P s →
        value P (fun _ => σ) s ≤ value P π s) := by sorry

end SurgeAppt.FirstAvail
