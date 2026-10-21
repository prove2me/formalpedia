-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_theorem_2
-- name    : SqrtAgreement.SRA.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:47.652923+00:00
-- url     : https://prove2.me/theorems/dc6c8f91-9541-4830-b713-777848275e95
-- title:
--   Theorem 2, p. 28 — for N large, symmetric fully informative profiles are strict BNE under SRA and every symmetric BNE pays at most ω more
-- statement:
--   Fix a finite answer set $\mathcal Y$, a bound $n$ on the number of tasks per agent, $\alpha>0$, $K>0$ and $\omega>0$. Then there is a positive integer $N_0$, depending only on $\alpha,\omega,n,K,|\mathcal Y|$, such that for every valid $\alpha$-separated generating model $(P_X,\mathbf p)$ (commonly known to the agents), every number of tasks $N>N_0$, every population with $|\mathcal M_i|\ge2$ for all tasks and $|\mathcal N_j|\le n$ for all agents, and every legal choice of the pairs $j_1(i)\neq j_2(i)$ and of the peers in Mechanism 1, under SRA:
--
--   1. every symmetric fully informative strategy profile (all agents report $\sigma(y)$ after observing $y$, for a common permutation $\sigma$ of $\mathcal Y$) is a strict Bayes–Nash equilibrium;
--   2. every symmetric Bayes–Nash equilibrium, in which all agents use a common stochastic reporting strategy $\mathbf q$, gives each agent $j$ an expected payment at most $\omega$ higher than any symmetric fully informative profile:
--   $$\mathbb E_{\mathbf q}[\tau_j]\ \le\ \mathbb E_{\sigma}[\tau_j]+\omega .$$
--
--   Thus, with many tasks, truthful reporting is an approximately payoff-optimal strict equilibrium among all symmetric equilibria, for every $\alpha$-separated model at once.
--
--   **Formalization Note** The model is valid and strategies are stochastic; $j_1(i)\neq j_2(i)$ and peer $\neq j$ formalize "any two agents" and "another agent"; the printed "$\mathcal N_j\le n$" is read as $|\mathcal N_j|\le n$. $N_0$ is chosen before the model, the population, the allocation and the mechanism's choices. "Any other symmetric BNE" is formalized over all symmetric BNE; for the fully informative ones the inequality holds with equality. The expected payoff is the agent's total expected payment over her tasks, computed as an explicit finite sum under the product law (since $|\mathcal N_j|\le n$ and $\omega$ is arbitrary, this is equivalent to the per-task reading of the proof). Expected payments are not defined through the limit formulas $K\Gamma$.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, p. 28, Theorem 2

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem theorem_2 (k n : ℕ) (α K ω : ℝ) (hα : 0 < α) (hK : 0 < K) (hω : 0 < ω) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ (m : ℕ) (G : GenModel m k), G.Valid → G.AlphaSeparated α →
      ∀ (N M : ℕ), N0 < N → ∀ S : Setting N M, S.Valid n →
        (∀ σ : Equiv.Perm (Fin k), IsStrictBNE G K S (symm (permStrat σ))) ∧
        (∀ q : Strat k, Stoch q → IsBNE G K S (symm q) →
          ∀ (σ : Equiv.Perm (Fin k)) (j : Fin M),
            expPay G K S (symm q) j ≤ expPay G K S (symm (permStrat σ)) j + ω) := by sorry

end SqrtAgreement.SRA
