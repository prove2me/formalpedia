-- Prove2me | Theorems.Thm_TwoAgentSched_Knapsack_theorem_5_2_equivalence
-- name    : TwoAgentSched.Knapsack.theorem_5_2_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:44.930586+00:00
-- url     : https://prove2.me/theorems/004ce371-054c-49fb-a875-cca94d6890d5
-- title:
--   Proof of Theorem 5.2 — KNAPSACK is a yes-instance iff the constructed instance meets $Q_A$, $Q_B$
-- statement:
--   Let $(u,w,b,W)$ be a KNAPSACK instance with $n$ items and $\sum_{i=1}^n w_iu_i>0$. With $\hat u=\sum_iu_i$, $\hat w=\sum_iw_i$, consider the two-agent instance with $A$-jobs $p^A_i=u_i$, $w^A_i=w_i$, one $B$-job with $p^B_1=\hat w\hat u$, and thresholds $Q_B=b+p^B_1$, $Q_A=\hat w\hat u+(\hat w-W)p^B_1$. Then
--
--   $$\exists\,S\subseteq\{1,\dots,n\}:\ \sum_{i\in S}u_i\le b,\ \sum_{i\in S}w_i\ge W\quad\Longleftrightarrow\quad\exists\,\sigma:\ \sum_{i=1}^nw_iC^A_i(\sigma)\le Q_A,\ C^B_1(\sigma)\le Q_B,$$
--
--   where $\sigma$ ranges over the sequences of all $n+1$ jobs processed without idle time from time $0$.
--
--   This combines the two directions of the proof of Theorem 5.2 into the correctness statement of the reduction.
--
--   **Formalization Note** The hypothesis $\sum_iw_iu_i>0$ is needed for the direction from schedules to KNAPSACK (see the counterexample in the statement of Eq. (2)). The thresholds are integers that may be negative; they are compared as real numbers with the completion times.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, proof of Theorem 5.2

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Problem51
import Definitions.Def_TwoAgentSched_Knapsack_Construction

namespace TwoAgentSched.Knapsack

/-- Proof of Theorem 5.2 (Agnetis et al. 2004, p. 233), both directions together: if
`∑_i w_i u_i > 0`, the KNAPSACK instance `(u, w, b, W)` is a yes-instance iff the constructed
instance of `1‖∑ w_iC^A_i ≤ Q_A, C^B_max ≤ Q_B` with `Q_A = ŵû + (ŵ - W)p^B_1` and
`Q_B = b + p^B_1` is a yes-instance. -/
theorem theorem_5_2_equivalence {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ)
    (hpos : 0 < ∑ i, w i * u i) :
    KnapsackYes u w b W ↔
      (construction u w).RecYes ((QA u w W : ℤ) : ℝ) ((QB u w b : ℤ) : ℝ) := by sorry

end TwoAgentSched.Knapsack
