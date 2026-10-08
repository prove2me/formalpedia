-- Prove2me | Theorems.Thm_ThomsonKS_Char_replica_problem_exists
-- name    : ThomsonKS.Char.replica_problem_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:50.745374+00:00
-- url     : https://prove2.me/theorems/ca39916b-9e8e-4ef1-8da6-74f68a06f420
-- title:
--   Appendix, proof of Theorem 2, p. 325 — the replica problem T ∈ Σ^Q with |Q| = 3|P| − 2 in which every agent faces a copy of agent 1's position in S
-- statement:
--   Let $P$ be a finite group of agents, $i_0 \in P$, and $S \in \Sigma^P$ a division problem normalized so that its ideal point is $a(S) = e^P$ (all coordinates $1$). Let $a \ge 0$ be such that $a\,e^P \in S$. Then there is a larger group $Q \supseteq P$ with
--
--   $$|Q| = 3|P| - 2$$
--
--   and a division problem $T \in \Sigma^Q$ such that
--
--   1. $T \cap \mathbb R^P = S$ (the zero-extension of $x \in \mathbb R^P$ lies in $T$ exactly when $x \in S$);
--   2. $a\,e^Q \in T$;
--   3. for every agent $j \in Q$ there is a group $P_j \subseteq Q$ with $j \in P_j$ and a bijection $\sigma : P \to P_j$ with $\sigma(i_0) = j$ such that $T \cap \mathbb R^{P_j}$ is the relabelling of $S$ along $\sigma$, i.e. $T \cap \mathbb R^{P_j} = \{x' : \exists x \in S,\ x'_{\sigma(i)} = x_i\ \forall i \in P\}$.
--
--   In words: every member of $Q$ faces, in a subproblem of $T$, an exact replica of the position held by agent $i_0$ in $S$. This is the construction on which the general proof of Theorem 2 rests; the paper builds $Q = P \cup P^2 \cup P^3$ with $P^1 = P \setminus\{i_0\}$ and $|P^2| = |P^3| = |P^1|$, and $T = \mathrm{cch}\{S, S^i, x^*\}$ with $x^* = a e^Q$, and asserts that $T \in \Sigma^Q$, $T \cap \mathbb R^P = S$ and $T \cap \mathbb R^{P_i} = S^i$.
--
--   **Formalization Note** The page fixes $i_0 = 1$ after an application of An; here $i_0$ is any member of $P$, a harmless generalization. The page's explicit construction (the sets $P^2, P^3$, the bijections $\gamma^1, \gamma^2$, the replicas $S^i$ and the hull $T$) is stated existentially: what the proof of Theorem 2 uses is the existence of $Q$, $T$ and the replica subproblems with the listed properties. The cardinality $3|P| - 2$ is the count the paper states in §4.2 (p. 323) for this construction; since $i_0 \in P$, $|P| \ge 1$ and the natural-number subtraction is exact.
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), p. 325, Appendix, proof of Theorem 2 (the construction of T and the claim 'It is clear that T is in Σ^Q, that T ∩ R^P = S and for each i ..., T ∩ R^{P_i} = S^i'); cardinality 3|P| − 2 from §4.2, p. 323

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

theorem replica_problem_exists (P : Finset ℕ) (i₀ : ℕ) (hi₀ : i₀ ∈ P) (S : Set (P → ℝ))
    (hS : S ∈ DivProb P) (ha : idealPt S = fun _ => 1) (a : ℝ) (haS : (fun _ => a) ∈ S) :
    ∃ Q : Finset ℕ, ∃ hPQ : P ⊆ Q, Q.card = 3 * P.card - 2 ∧
      ∃ T ∈ DivProb Q, {x | zeroExt hPQ x ∈ T} = S ∧ (fun _ => a) ∈ T ∧
        ∀ j ∈ Q, ∃ Pj : Finset ℕ, ∃ hPj : Pj ⊆ Q, ∃ hj : j ∈ Pj,
          ∃ σ : P ≃ Pj, σ ⟨i₀, hi₀⟩ = ⟨j, hj⟩ ∧
            {x | zeroExt hPj x ∈ T} = relabel σ S := by sorry

end ThomsonKS.Char
