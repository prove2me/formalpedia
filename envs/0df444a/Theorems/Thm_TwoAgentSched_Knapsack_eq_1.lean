-- Prove2me | Theorems.Thm_TwoAgentSched_Knapsack_eq_1
-- name    : TwoAgentSched.Knapsack.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:45.584973+00:00
-- url     : https://prove2.me/theorems/63ffa263-f172-4cb3-a4ce-6620930b0c3e
-- title:
--   Proof of Theorem 5.2, Eq. (1) — a KNAPSACK solution yields a schedule meeting $Q_A$ and $Q_B$
-- statement:
--   Let $(u,w,b,W)$ be a KNAPSACK instance with $n$ items and consider the two-agent instance of the proof of Theorem 5.2: $A$-jobs with $p^A_i=u_i$, $w^A_i=w_i$, one $B$-job with $p^B_1=\hat w\hat u$, and thresholds $Q_B=b+p^B_1$, $Q_A=\hat w\hat u+(\hat w-W)p^B_1$, where $\hat u=\sum_iu_i$, $\hat w=\sum_iw_i$.
--
--   Let $S\subseteq\{1,\dots,n\}$ solve KNAPSACK, i.e. $\sum_{i\in S}u_i\le b$ and $\sum_{i\in S}w_i\ge W$, and let $\sigma$ be any sequence of all $n+1$ jobs in which the $A$-jobs sequenced before the $B$-job are exactly those $J^A_i$ with $i\in S$. Then
--
--   $$C^B_1(\sigma)\le Q_B\qquad\text{and}\qquad\sum_{i=1}^n w_iC^A_i(\sigma)\le Q_A .$$
--
--   This is the "KNAPSACK yes $\Rightarrow$ schedule yes" direction of the reduction.
--
--   **Formalization Note** The paper writes the two estimates on the terms of (1) as strict ("smaller than"); they hold only with $\le$ (with $n=1$, $u_1=w_1=1$, $S=\{1\}$, $b=W=1$, the cost equals $Q_A$), and only $\le$ is needed, so the statement uses $\le$. The statement holds for every order of the jobs within $S$ and within its complement. No positivity assumption is needed in this direction.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, proof of Theorem 5.2, Eq. (1)

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Construction

namespace TwoAgentSched.Knapsack

/-- Proof of Theorem 5.2, Eq. (1) (Agnetis et al. 2004, p. 233): from a KNAPSACK solution `S`
(`∑_{i∈S} u_i ≤ b`, `∑_{i∈S} w_i ≥ W`), every sequence of the constructed instance in which the
A-jobs placed before the B-job are exactly those of `S` meets both thresholds `Q_A` and `Q_B`. -/
theorem eq_1 {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) (S : Finset (Fin n))
    (hu : ((∑ i ∈ S, u i : ℕ) : ℤ) ≤ b) (hw : W ≤ ((∑ i ∈ S, w i : ℕ) : ℤ))
    (l : List (Fin (construction u w).nA ⊕ Fin (construction u w).nB))
    (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hS : ∀ i : Fin n, i ∈ S ↔ l.idxOf (aJob u w i) < l.idxOf (bJob u w)) :
    (construction u w).Meets ((QA u w W : ℤ) : ℝ) ((QB u w b : ℤ) : ℝ) l := by sorry

end TwoAgentSched.Knapsack
