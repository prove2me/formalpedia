-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_spt_total_eq_T
-- name    : TwoAgentSched.TotalTotal.spt_total_eq_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:04.330596+00:00
-- url     : https://prove2.me/theorems/1ae776ed-175f-46e7-950d-07cda3b03ca0
-- title:
--   Proof of Theorem 9.2 — every SPT schedule has $\sum C^A_i+\sum C^B_i=T$, and $Q_A=Q_B=T/2$
-- statement:
--   Let $p_1\le p_2\le\dots\le p_k$ be nonnegative integers, $P=\sum_ip_i$, and consider the two-agent instance of the proof of Theorem 9.2, in which agents $A$ and $B$ each have $k$ jobs of lengths $p_1,\dots,p_k$. For every SPT schedule $\sigma$ (the pairs $J[1],\dots,J[k]$ in this order, each pair in either internal order),
--
--   $$\sum_{i=1}^kC^A_i(\sigma)+\sum_{i=1}^kC^B_i(\sigma)=T=3P+4\sum_{i=1}^k(k-i)p_i ,$$
--
--   and the threshold $Q_A=Q_B=\tfrac32P+2\sum_{i=1}^k(k-i)p_i$ of the construction equals $T/2$.
--
--   The overall total completion time therefore does not depend on which agent goes first in each pair; this is the reference value against which feasibility is measured in the rest of the proof.
--
--   **Formalization Note** The SPT schedule is given by the choice $x:\mathrm{Fin}\,k\to\mathrm{Bool}$ of the first agent in each pair. The sortedness hypothesis is the paper's numbering convention.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 237, proof of Theorem 9.2 ("Also, note that … Q_A = Q_B = T/2")

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

/-- Proof of Theorem 9.2 (Agnetis et al. 2004, p. 237): for integers `p_1 ≤ ⋯ ≤ p_k`, every SPT
schedule of the constructed instance has the same overall total completion time
`∑ C^A_i + ∑ C^B_i = T = 3P + 4 ∑_{i=1}^k (k - i) p_i`, and the threshold `Q_A = Q_B` equals
`T / 2`. -/
theorem spt_total_eq_T {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p) (x : Fin k → Bool) :
    (construction p).sumCA (sptSeq x) + (construction p).sumCB (sptSeq x) = (bigT p : ℝ) ∧
      thresholdQ p = (bigT p : ℝ) / 2 := by sorry

end TwoAgentSched.TotalTotal
