-- Prove2me | Theorems.Thm_TwoAgentSched_Knapsack_eq_2
-- name    : TwoAgentSched.Knapsack.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:49.082352+00:00
-- url     : https://prove2.me/theorems/48f45795-d107-4232-b76a-b65f57551a34
-- title:
--   Proof of Theorem 5.2, Eq. (2) — the A-jobs before the B-job of a feasible schedule solve KNAPSACK
-- statement:
--   Let $(u,w,b,W)$ be a KNAPSACK instance with $n$ items such that
--
--   $$\sum_{i=1}^n w_iu_i>0,$$
--
--   and consider the two-agent instance of the proof of Theorem 5.2 ($p^A_i=u_i$, $w^A_i=w_i$, one $B$-job with $p^B_1=\hat w\hat u$, $Q_B=b+p^B_1$, $Q_A=\hat w\hat u+(\hat w-W)p^B_1$). If a sequence $\sigma$ of all $n+1$ jobs satisfies $\sum_iw_iC^A_i(\sigma)\le Q_A$ and $C^B_1(\sigma)\le Q_B$, then the set $S$ of indices of the $A$-jobs sequenced before the $B$-job satisfies
--
--   $$\sum_{i\in S}u_i\le b\qquad\text{and}\qquad\sum_{i\in S}w_i\ge W .$$
--
--   This is the "schedule yes $\Rightarrow$ KNAPSACK yes" direction of the reduction.
--
--   **Formalization Note** The hypothesis $\sum_iw_iu_i>0$ is added: the strict inequalities of (2) need it. Without it the statement is false: for $n=1$, $u_1=0$, $w_1=1$, $b=0$, $W=2$ one gets $p^B_1=0$, $Q_A=Q_B=0$, every sequence meets both thresholds, yet no subset has $\sum_{i\in S}w_i\ge2$. Instances with $\sum_iw_iu_i=0$ are handled separately by the reduction of Theorem 5.2.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, proof of Theorem 5.2, Eq. (2)

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Construction

namespace TwoAgentSched.Knapsack

/-- Proof of Theorem 5.2, Eq. (2) (Agnetis et al. 2004, p. 233): if `∑_i w_i u_i > 0` and a
sequence `l` of the constructed instance meets both thresholds `Q_A` and `Q_B`, then the set `S`
of A-jobs sequenced before the B-job solves KNAPSACK: `∑_{i∈S} u_i ≤ b` and `∑_{i∈S} w_i ≥ W`. -/
theorem eq_2 {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) (hpos : 0 < ∑ i, w i * u i)
    (l : List (Fin (construction u w).nA ⊕ Fin (construction u w).nB))
    (hl : (construction u w).Meets ((QA u w W : ℤ) : ℝ) ((QB u w b : ℤ) : ℝ) l) :
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => l.idxOf (aJob u w i) < l.idxOf (bJob u w)),
        u i : ℕ) : ℤ) ≤ b ∧
      W ≤ ((∑ i ∈ Finset.univ.filter (fun i : Fin n => l.idxOf (aJob u w i) < l.idxOf (bJob u w)),
        w i : ℕ) : ℤ) := by sorry

end TwoAgentSched.Knapsack
