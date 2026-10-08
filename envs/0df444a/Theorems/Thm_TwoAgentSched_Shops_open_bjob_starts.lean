-- Prove2me | Theorems.Thm_TwoAgentSched_Shops_open_bjob_starts
-- name    : TwoAgentSched.Shops.open_bjob_starts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:56.188603+00:00
-- url     : https://prove2.me/theorems/d56ea047-3ccc-4015-9e93-a5a7a0e797c1
-- title:
--   Proof of Theorem 10.2 — $C^B_{\max}\le P$ forces the B-job to start at $0$ on one machine and at $P/2$ on the other
-- statement:
--   Let $p_1,\dots,p_k$ be nonnegative integers, $P=\sum_i p_i$, and consider the open shop instance of the proof of Theorem 10.2: $k$ A-jobs with processing time $p_i$ on both machines and one B-job $J^B_1$ with processing time $P/2$ on both machines.
--
--   Let $s_1,s_2$ be the start times of a feasible open shop schedule in which both operations of $J^B_1$ end by $Q_B=P$. Then
--   $$\bigl(s_1(J^B_1)=0\ \text{and}\ s_2(J^B_1)=\tfrac P2\bigr)\quad\text{or}\quad\bigl(s_2(J^B_1)=0\ \text{and}\ s_1(J^B_1)=\tfrac P2\bigr).$$
--
--   The B-job thus occupies one machine during $[0,P/2]$ and the other during $[P/2,P]$, which fixes the gaps left for the A-jobs.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 239, proof of Theorem 10.2 ("The constraint C^B_max ⩽ Q_B = P can be satisfied only if …")

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction

namespace TwoAgentSched.Shops

/-- Proof of Theorem 10.2 (Agnetis et al. 2004, p. 239): in the open shop instance built from the
PARTITION integers `p`, every feasible schedule meeting `C^B_max ≤ Q_B = P` starts the B-job at
time `0` on one machine and at time `P/2` on the other. -/
theorem open_bjob_starts (p : List ℕ)
    (s₁ s₂ : Fin ((openInst p).nA + (openInst p).nB) → ℝ)
    (hfeas : IsOpenFeasible (openInst p).p1 (openInst p).p2 s₁ s₂)
    (hB : (openInst p).MeetsB s₁ s₂ (openQB p)) :
    (s₁ (openB p) = 0 ∧ s₂ (openB p) = partSum p / 2) ∨
      (s₂ (openB p) = 0 ∧ s₁ (openB p) = partSum p / 2) := by sorry

end TwoAgentSched.Shops
