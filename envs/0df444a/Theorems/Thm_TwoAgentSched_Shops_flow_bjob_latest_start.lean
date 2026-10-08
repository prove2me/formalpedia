-- Prove2me | Theorems.Thm_TwoAgentSched_Shops_flow_bjob_latest_start
-- name    : TwoAgentSched.Shops.flow_bjob_latest_start
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:30.717354+00:00
-- url     : https://prove2.me/theorems/f678faf9-6269-4369-b970-f1d34b59ef66
-- title:
--   Proof of Theorem 10.1 — $C^B_{\max}\le P+\varepsilon$ forces the B-job to start on $M_2$ by $P/2+\varepsilon$
-- statement:
--   Let $p_1,\dots,p_k$ be nonnegative integers, $P=\sum_i p_i$, $\varepsilon=1/(k+1)$, and consider the flow shop instance built from them in the proof of Theorem 10.1: $k$ A-jobs with processing times $\varepsilon$ on $M_1$ and $p_i$ on $M_2$, one B-job $J^B_1$ with processing times $P/2-(k-1)\varepsilon$ on $M_1$ and $P/2$ on $M_2$.
--
--   Let $s_1, s_2$ be the start times on $M_1$, $M_2$ of a feasible flow shop schedule in which both operations of $J^B_1$ end by $Q_B=P+\varepsilon$. Then
--   $$s_2(J^B_1)\le \frac P2+\varepsilon\qquad\text{and}\qquad \sum_{i:\ s_2(J^A_i)<s_2(J^B_1)} p_i\le \frac P2,$$
--   i.e. the B-job starts on the second machine by $P/2+\varepsilon$, and the A-jobs started on the second machine before it have total length at most $P/2$.
--
--   This is the first half of the argument that a feasible schedule splits the integers into two halves.
--
--   **Formalization Note** "The A-jobs preceding $J^B_1$ on the second machine" is read as those whose $M_2$ operation starts strictly before that of $J^B_1$ (an A-job of length $0$ may share the start time; it adds nothing to the sum).
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, proof of Theorem 10.1 ("The constraint C^B_max ⩽ Q_B = P + ε can be satisfied only if …")

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction

namespace TwoAgentSched.Shops

/-- Proof of Theorem 10.1 (Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, p. 238): in the flow
shop instance built from the PARTITION integers `p`, every feasible schedule meeting
`C^B_max ≤ Q_B = P + ε` starts the B-job on `M_2` not after `P/2 + ε`, and the A-jobs started on
`M_2` before the B-job have total `M_2` processing time `∑ p_i ≤ P/2`. -/
theorem flow_bjob_latest_start (p : List ℕ)
    (s₁ s₂ : Fin ((flowInst p).nA + (flowInst p).nB) → ℝ)
    (hfeas : JohnsonFlowShop.TwoStage.IsFeasible (flowInst p).p1 (flowInst p).p2 s₁ s₂)
    (hB : (flowInst p).MeetsB s₁ s₂ (flowQB p)) :
    s₂ (flowB p) ≤ partSum p / 2 + eps p ∧
      ∑ i ∈ Finset.univ.filter (fun i : Fin p.length => s₂ (flowA p i) < s₂ (flowB p)),
        (p.get i : ℝ) ≤ partSum p / 2 := by sorry

end TwoAgentSched.Shops
