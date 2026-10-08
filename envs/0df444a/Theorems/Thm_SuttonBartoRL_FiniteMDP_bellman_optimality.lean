-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_bellman_optimality
-- name    : SuttonBartoRL.FiniteMDP.bellman_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:50:31.720275+00:00
-- url     : https://prove2.me/theorems/cc9fc5dd-d1ed-4f78-b0d6-95ec2ce6fcde
-- title:
--   §3.6: an optimal policy exists, $v_*$ is the unique solution of (3.19), and greedy policies are optimal
-- statement:
--   Consider a finite MDP with states $\mathcal S$, a nonempty finite action set $\mathcal A$, dynamics $p(s', r \mid s, a)$, and a discount rate $0 \le \gamma < 1$. For a stochastic policy $\pi$ let $v_\pi$ be its state-value function (3.12), the expected discounted return, and let $v_*(s) = \max_\pi v_\pi(s)$ (3.15). Then:
--
--   1. For every state $s$ the maximum defining $v_*(s)$ is attained by some policy.
--   2. There is an **optimal policy** $\pi_*$: $v_{\pi_*}(s) \ge v_\pi(s)$ for every policy $\pi$ and every state $s$.
--   3. $v_*$ satisfies the **Bellman optimality equation**
--   $$v_*(s) = \max_a \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v_*(s')\big] \quad \text{for all } s \in \mathcal S. \qquad (3.19)$$
--   4. $v_*$ is the **unique** function on $\mathcal S$ satisfying (3.19).
--   5. Every policy that assigns nonzero probability only to actions at which the maximum in (3.19) is obtained is an optimal policy.
--
--   This is the central result of Chapter 3: an optimal policy exists, its value is characterized by a system of $|\mathcal S|$ nonlinear equations with a unique solution, and once $v_*$ is known an optimal policy is obtained by a one-step greedy search. Dynamic programming (Chapter 4) and the control algorithms of Part I rest on it.
--
--   **Formalization Note** The book states these facts for finite MDPs, including episodic tasks with $\gamma = 1$; the statement covers $0 \le \gamma < 1$, since for $\gamma = 1$ uniqueness requires that every policy terminates, a hypothesis the book does not state. The book's action sets $\mathcal A(s)$ are replaced by one set $\mathcal A$ (its footnote 3). $v_\pi$ is defined from expected returns and $v_*$ as a supremum over stochastic policies; part 1 shows the supremum is a maximum.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §3.6, Eq. (3.15), p. 62; Eqs. (3.18)–(3.19), p. 63; uniqueness and greedy policies, p. 64

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., §3.6, pp. 62–64, Eqs. (3.15), (3.19). For a finite MDP with a single
nonempty finite action set and `0 ≤ γ < 1`:
1. (3.15) the maximum `v_*(s) = max_π v_π(s)` over stochastic policies is attained at every state;
2. there is an optimal policy, better than or equal to every policy at every state;
3. (3.19) `v_*(s) = max_a Σ_{s',r} p(s', r|s, a) [r + γ v_*(s')]` for all `s`;
4. `v_*` is the unique solution of (3.19);
5. every policy that assigns nonzero probability only to actions attaining the maximum in (3.19)
   is optimal. -/
theorem bellman_optimality {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∀ s, IsGreatest (Set.range fun π : Policy S A => stateValue M γ π s) (optimalValue M γ s)) ∧
    (∃ πstar : Policy S A, IsOptimalPolicy M γ πstar) ∧
    (∀ s, optimalValue M γ s = Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * optimalValue M γ s'))) ∧
    (∀ v : S → ℝ, (∀ s, v s = Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s'))) → v = optimalValue M γ) ∧
    (∀ π : Policy S A,
      (∀ s a, 0 < π.prob s a →
        ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * optimalValue M γ s') =
          Finset.univ.sup' Finset.univ_nonempty
            (fun b => ∑ s', ∑ r ∈ M.R, M.p s b s' r * (r + γ * optimalValue M γ s'))) →
      IsOptimalPolicy M γ π) := by sorry

end SuttonBartoRL.FiniteMDP
