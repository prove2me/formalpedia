-- Prove2me | Theorems.Thm_TwoAgentSched_Shops_theorem_10_1_equivalence
-- name    : TwoAgentSched.Shops.theorem_10_1_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:14.836911+00:00
-- url     : https://prove2.me/theorems/224bb3cd-e042-4b46-883f-4190047e9eb5
-- title:
--   Proof of Theorem 10.1 — for even $P$, PARTITION yes iff the flow shop instance meets $Q_A$ and $Q_B$
-- statement:
--   Let $p_1,\dots,p_k$ be nonnegative integers with $P=\sum_i p_i$ **even**, and assume moreover $P\ge 2$ or $k\le 1$. Consider the flow shop instance of the proof of Theorem 10.1 ($\varepsilon=1/(k+1)$; A-jobs with times $\varepsilon$ on $M_1$ and $p_i$ on $M_2$; one B-job with times $P/2-(k-1)\varepsilon$ and $P/2$) with thresholds $Q_A=3P/2+\varepsilon$ and $Q_B=P+\varepsilon$. Then
--   $$\exists\, S\subseteq\{1,\dots,k\}:\ \sum_{i\in S}p_i=\sum_{i\notin S}p_i \iff \text{some feasible flow shop schedule has } C^A_{\max}\le Q_A \text{ and } C^B_{\max}\le Q_B.$$
--
--   This equivalence is the correctness of the reduction of PARTITION to $F2\|C^A_{\max}\le Q_A, C^B_{\max}\le Q_B$.
--
--   **Formalization Note** The paper states the equivalence for every instance and uses $\lfloor P/2+k\varepsilon\rfloor=P/2$, which needs $P$ even. For odd $P$ it fails: $p=(1)$ gives $\varepsilon=1/2$, and the schedule $M_1$: B on $[0,1/2]$, A on $[1/2,1]$; $M_2$: B on $[1/2,1]$, A on $[1,2]$ meets $Q_A=2$, $Q_B=3/2$, while $(1)$ has no partition. For $P=0$ and $k\ge 2$ it fails too ($k$ operations of length $\varepsilon$ cannot all end on $M_1$ by $Q_A=\varepsilon$, while all-zero integers partition); the hypothesis "$P\ge 2$ or $k\le 1$" excludes exactly the even cases in which the printed $p^B_{11}$ is negative. Odd $P$ is a no-instance of PARTITION, so a reduction can map it to a fixed no-instance.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, proof of Theorem 10.1 (the equivalence, with Figure 2)

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction

namespace TwoAgentSched.Shops

open ProjSchedTW.Complexity

/-- Proof of Theorem 10.1 (Agnetis et al. 2004, p. 238), the equivalence, for an even total
`P = ∑ p_i` with `P ≥ 2` or at most one integer (among even totals these are exactly the cases
with `p^B_{11} = P/2 − (k − 1)ε ≥ 0`): the PARTITION instance `p` is a yes-instance iff the
constructed flow shop instance has a feasible schedule with `C^A_max ≤ 3P/2 + ε` and
`C^B_max ≤ P + ε`. (For odd `P` the printed equivalence fails: `p = [1]`.) -/
theorem theorem_10_1_equivalence (p : List ℕ) (heven : Even p.sum)
    (hrange : 2 ≤ p.sum ∨ p.length ≤ 1) :
    PartitionYes p ↔ (flowInst p).FlowYes (flowQA p) (flowQB p) := by sorry

end TwoAgentSched.Shops
