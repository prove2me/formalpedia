-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_feasible_is_spt
-- name    : TwoAgentSched.TotalTotal.feasible_is_spt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:00.180264+00:00
-- url     : https://prove2.me/theorems/3b377dd6-f815-45ff-990c-08700b647adc
-- title:
--   Proof of Theorem 9.2 — a schedule with $\sum C^A_i\le T/2$ and $\sum C^B_i\le T/2$ is SPT
-- statement:
--   Let $p_1\le\dots\le p_k$ be nonnegative integers, $P=\sum_ip_i$ and $T=3P+4\sum_{i=1}^k(k-i)p_i$, and consider the instance of the proof of Theorem 9.2, in which agents $A$ and $B$ each have $k$ jobs of lengths $p_1,\dots,p_k$. If a sequence $\sigma$ of all $2k$ jobs satisfies
--
--   $$\sum_{i=1}^kC^A_i(\sigma)\le T/2\qquad\text{and}\qquad\sum_{i=1}^kC^B_i(\sigma)\le T/2,$$
--
--   then $\sigma$ is SPT: the processing times of the jobs, read along $\sigma$, are nondecreasing.
--
--   Feasibility thus forces the shortest-processing-time order, which is where the two agents' totals become controlled by (5) and (6).
--
--   **Formalization Note** "SPT" here means nondecreasing lengths along the sequence. That is what the paper's exchange argument establishes. The stronger reading, that $\sigma$ consists of the consecutive pairs $J[1],\dots,J[k]$, fails when lengths repeat: for $p=(1,1,1,1,10)$ the sequence with agents $B,B,A,B,A,B,A,A,A,B$ (lengths $1,\dots,1,10,10$) has $\sum C^A=\sum C^B=41=T/2$ but is not a sequence of consecutive pairs. For pairwise distinct lengths the two readings coincide.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 237–238, proof of Theorem 9.2 ("We next prove that if a feasible schedule σ … then σ is an SPT schedule")

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

/-- Proof of Theorem 9.2 (Agnetis et al. 2004, pp. 237–238): for integers `p_1 ≤ ⋯ ≤ p_k`, every
sequence `l` of all `2k` jobs of the constructed instance that is feasible for
`1‖∑ C^A_i ≤ T/2, ∑ C^B_i ≤ T/2` processes the jobs in nondecreasing order of length
(it is SPT). -/
theorem feasible_is_spt {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p)
    (l : List (Fin k ⊕ Fin k))
    (hl : (construction p).Meets ((bigT p : ℝ) / 2) ((bigT p : ℝ) / 2) l) :
    (l.map (construction p).p).Pairwise (· ≤ ·) := by sorry

end TwoAgentSched.TotalTotal
