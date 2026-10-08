-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_theorem_9_2_equivalence
-- name    : TwoAgentSched.TotalTotal.theorem_9_2_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:58.796973+00:00
-- url     : https://prove2.me/theorems/83733960-56ec-4fcd-b86c-72592fdad570
-- title:
--   Proof of Theorem 9.2 — for distinct $p_1<\dots<p_k$, PARTITION is yes iff some schedule meets $T/2$ for both agents
-- statement:
--   Let $p_1<p_2<\dots<p_k$ be pairwise distinct nonnegative integers, $P=\sum_ip_i$, $T=3P+4\sum_{i=1}^k(k-i)p_i$, and consider the instance of the proof of Theorem 9.2, in which agents $A$ and $B$ each have $k$ jobs of lengths $p_1,\dots,p_k$. Then
--
--   $$\exists\,S\subseteq\{1,\dots,k\}:\ \sum_{i\in S}p_i=\sum_{i\notin S}p_i\quad\Longleftrightarrow\quad\exists\,\sigma:\ \sum_{i=1}^kC^A_i(\sigma)\le T/2,\ \sum_{i=1}^kC^B_i(\sigma)\le T/2,$$
--
--   where $\sigma$ ranges over the sequences of all $2k$ jobs processed without idle time from time $0$.
--
--   This is the correctness statement of the reduction of Theorem 9.2, for PARTITION instances without repeated values.
--
--   **Formalization Note** The paper states the equivalence for $p_1\le\dots\le p_k$. With repeated values it is false: for $p=(1,1,1,1,10)$, PARTITION has no solution ($P=14$, and no subset sums to $7$), yet $T=82$ and the sequence with agents $B,B,A,B,A,B,A,A,A,B$ (lengths $1,1,1,1,1,1,1,1,10,10$) gives $\sum C^A=3+5+7+8+18=41$ and $\sum C^B=1+2+4+6+28=41$. The paper's step "only SPT schedules can be feasible", followed by (5) and (6), assumes that a feasible schedule consists of consecutive pairs, which holds only when the lengths are distinct. The statement therefore assumes $p$ strictly increasing. PARTITION is the published `PartitionYes` applied to the list $p_1,\dots,p_k$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, proof of Theorem 9.2 ("For a schedule to be feasible … solution to the instance of Partition"); corrected

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

open ProjSchedTW.Complexity

/-- Proof of Theorem 9.2 (Agnetis et al. 2004, p. 238), corrected: for pairwise distinct integers
`p_1 < p_2 < ⋯ < p_k`, the PARTITION instance `{p_1, …, p_k}` is a yes-instance iff the
constructed instance has a sequence of all jobs with `∑ C^A_i ≤ T/2` and `∑ C^B_i ≤ T/2`.
(With repeated lengths the printed equivalence fails, e.g. for `1, 1, 1, 1, 10`.) -/
theorem theorem_9_2_equivalence {k : ℕ} (p : Fin k → ℕ) (hp : StrictMono p) :
    PartitionYes (List.ofFn p) ↔
      (construction p).RecYes ((bigT p : ℝ) / 2) ((bigT p : ℝ) / 2) := by sorry

end TwoAgentSched.TotalTotal
