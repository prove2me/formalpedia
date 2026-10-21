-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_theorem_1
-- name    : SqrtAgreement.SRA.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:57.276507+00:00
-- url     : https://prove2.me/theorems/2fb9e81a-e68a-4615-8bb1-df7c929613c2
-- title:
--   Theorem 1, pp. 24–25 — for N large, SRA is strictly Bayes–Nash incentive compatible and truthful beats observation-independent reporting by ω
-- statement:
--   Fix a finite answer set $\mathcal Y$, a bound $n$ on the number of tasks per agent, $\alpha>0$, $K>0$, and $\omega$ with
--   $$0<\omega<\alpha K(|\mathcal Y|-1).$$
--   Then there is a positive integer $N_0$, depending only on $\omega,\alpha,|\mathcal Y|,n,K$, such that for every valid $\alpha$-separated generating model $(P_X,\mathbf p)$ (commonly known to the agents), every number of tasks $N>N_0$, every population with $|\mathcal M_i|\ge2$ for all tasks and $|\mathcal N_j|\le n$ for all agents, and every legal choice of the pairs $j_1(i)\neq j_2(i)$ and of the peers in Mechanism 1, under SRA:
--
--   1. the truthful strategy profile is a strict Bayes–Nash equilibrium (SRA is strictly Bayes–Nash incentive compatible with respect to $(P_X,\mathbf p)$);
--   2. for every agent $j$ who performs at least one task, if everyone else is truthful and $j$ instead uses on each of her tasks a reporting strategy whose report is independent of her observation, then her expected payment is at least $\omega$ lower than under truthful reporting.
--
--   The theorem shows that the mechanism needs no knowledge of $(P_X,\mathbf p)$ beyond $\alpha$-separation, and that the gain from truthful reporting over effortless reporting is bounded away from zero.
--
--   **Formalization Note** The model is valid (probability vectors) and strategies are stochastic, as the page takes for granted. $j_1(i)\neq j_2(i)$ and peer $\neq j$ formalize "any two agents" and "another agent". The printed hypothesis "$\mathcal N_j\le n$" is read as $|\mathcal N_j|\le n$. In claim 2, $\mathcal N_j\neq\emptyset$ is added (otherwise both payments are $0$), and "a reporting strategy where the reported response is independent of her true response" is read as observation-independence on every task she performs. $N_0$ is chosen before the model, the population and the mechanism's choices. Expected payment is the agent's total over her tasks, computed as an explicit finite sum.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, pp. 24–25, Theorem 1

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem theorem_1 (k n : ℕ) (α K ω : ℝ) (hα : 0 < α) (hK : 0 < K) (hω : 0 < ω)
    (hωlt : ω < α * K * ((k : ℝ) - 1)) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ (m : ℕ) (G : GenModel m k), G.Valid → G.AlphaSeparated α →
      ∀ (N M : ℕ), N0 < N → ∀ S : Setting N M, S.Valid n →
        IsStrictBNE G K S (symm (truthful k)) ∧
        ∀ j : Fin M, (S.tasks j).Nonempty → ∀ Q' : Profile N M k,
          IsDeviation S (symm (truthful k)) Q' j →
          (∀ i ∈ S.tasks j, ObsIndependent (Q' i j)) →
          expPay G K S Q' j + ω ≤ expPay G K S (symm (truthful k)) j := by sorry

end SqrtAgreement.SRA
