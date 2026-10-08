-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_theorem_9_3
-- name    : TwoAgentSched.TotalTotal.theorem_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:16.318573+00:00
-- url     : https://prove2.me/theorems/302f95d1-efa3-4335-85ec-3f3fc5042356
-- title:
--   Theorem 9.3 with (7) — $F(n_A,n_B,Q)$ is the optimal value of $1\|\sum C^A_i:\sum C^B_i\le Q$
-- statement:
--   Consider a two-agent single-machine instance in which each agent's jobs are numbered in SPT order, $p^A_1\le\dots\le p^A_{n_A}$ and $p^B_1\le\dots\le p^B_{n_B}$, and let $Q\in\mathbb N$. Let $F$ be the dynamic program (7) with its initialisation. Then $F(n_A,n_B,Q)$ is the optimal value of the constrained problem
--
--   $$\min\Bigl\{\sum_{h=1}^{n_A}C^A_h(\sigma)\ :\ \sigma \text{ a sequence of all jobs},\ \sum_{k=1}^{n_B}C^B_k(\sigma)\le Q\Bigr\},$$
--
--   in the following sense:
--   1. $F(n_A,n_B,Q)=+\infty$ iff no sequence of all jobs has $\sum_kC^B_k\le Q$;
--   2. if $F(n_A,n_B,Q)=m$ is finite, then some sequence with $\sum_kC^B_k\le Q$ has $\sum_hC^A_h=m$, and every sequence with $\sum_kC^B_k\le Q$ has $\sum_hC^A_h\ge m$.
--
--   This is the correctness half of Theorem 9.3: the problem is solved by a pseudopolynomial dynamic program.
--
--   **Formalization Note** The running time $O(n_An_BQ)$ of Theorem 9.3 is not formalised. The SPT numbering of each agent's jobs is the paper's standing convention of §9 and is a hypothesis.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, Theorem 9.3 with recursion (7)

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_DP

namespace TwoAgentSched.TotalTotal

open MooreLateJobs.Shared

/-- Theorem 9.3 with recursion (7) (Agnetis et al. 2004, p. 238), correctness half: when each
agent's jobs are numbered in SPT order (`p^A_1 ≤ ⋯ ≤ p^A_{n_A}`, `p^B_1 ≤ ⋯ ≤ p^B_{n_B}`),
`F(n_A, n_B, Q)` is the optimal value of `1‖∑ C^A_i : ∑ C^B_i ≤ Q`:
1. `F(n_A, n_B, Q) = +∞` iff no sequence of all jobs has `∑ C^B_i ≤ Q`;
2. if `F(n_A, n_B, Q) = m` is finite, some sequence with `∑ C^B_i ≤ Q` has `∑ C^A_i = m`, and
   every sequence with `∑ C^B_i ≤ Q` has `∑ C^A_i ≥ m`.
The running time `O(n_A n_B Q)` is not part of the statement. -/
theorem theorem_9_3 (I : Instance) (hA : Monotone I.pA) (hB : Monotone I.pB) (Q : ℕ) :
    (I.dpF I.nA I.nB Q = ⊤ ↔
      ¬ ∃ l, IsSchedule Finset.univ l ∧ I.sumCB l ≤ (Q : ℝ)) ∧
    ∀ m : ℕ, I.dpF I.nA I.nB Q = (m : ℕ∞) →
      (∃ l, IsSchedule Finset.univ l ∧ I.sumCB l ≤ (Q : ℝ) ∧ I.sumCA l = (m : ℝ)) ∧
      ∀ l, IsSchedule Finset.univ l → I.sumCB l ≤ (Q : ℝ) → (m : ℝ) ≤ I.sumCA l := by sorry

end TwoAgentSched.TotalTotal
