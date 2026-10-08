-- Prove2me | Theorems.Thm_TwoAgentSched_Shops_theorem_10_2_equivalence
-- name    : TwoAgentSched.Shops.theorem_10_2_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:54.667132+00:00
-- url     : https://prove2.me/theorems/195626a7-c739-44a2-a47c-4c5f3a7db9b8
-- title:
--   Proof of Theorem 10.2 — PARTITION yes iff the open shop instance meets $Q_A=3P/2$ and $Q_B=P$
-- statement:
--   Let $p_1,\dots,p_k$ be nonnegative integers and $P=\sum_i p_i$. Consider the open shop instance of the proof of Theorem 10.2 (A-jobs with time $p_i$ on both machines, one B-job with time $P/2$ on both machines) with thresholds $Q_A=3P/2$ and $Q_B=P$. Then
--   $$\exists\, S\subseteq\{1,\dots,k\}:\ \sum_{i\in S}p_i=\sum_{i\notin S}p_i \iff \text{some feasible open shop schedule has } C^A_{\max}\le Q_A \text{ and } C^B_{\max}\le Q_B.$$
--
--   This equivalence is the correctness of the reduction of PARTITION to $O2\|C^A_{\max}\le Q_A, C^B_{\max}\le Q_B$; it holds for every $P$, odd included.
--
--   **Formalization Note** The printed proof says $\sum_{i=1}^{n_A}p^A_i+\sum_{i=1}^{n_B}p^B_i=2P$; what the argument uses is that each machine carries total work $P+P/2=3P/2=Q_A$. The statement is unaffected.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 239, proof of Theorem 10.2 (the equivalence, with Figure 3)

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction

namespace TwoAgentSched.Shops

open ProjSchedTW.Complexity

/-- Proof of Theorem 10.2 (Agnetis et al. 2004, p. 239), the equivalence: the PARTITION instance
`p` is a yes-instance iff the constructed open shop instance has a feasible schedule with
`C^A_max ≤ 3P/2` and `C^B_max ≤ P`. -/
theorem theorem_10_2_equivalence (p : List ℕ) :
    PartitionYes p ↔ (openInst p).OpenYes (openQA p) (openQB p) := by sorry

end TwoAgentSched.Shops
