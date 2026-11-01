-- Prove2me | Theorems.Thm_ShrinkingUCB_regret_le_lcb_sum
-- name    : ShrinkingUCB.regret_le_lcb_sum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:21.129776+00:00
-- url     : https://prove2.me/theorems/14b97b94-2b09-466e-a332-1a3f6a83ff3a
-- title:
--   Last display, p.19, first line — $R(T)$ is at most the LCB increase plus the widths
-- statement:
--   Let $K\le N$, $\alpha\ge0$, $|S^*|=K$. On every outcome table on which (4) holds,
--
--   $$
--   R(T)\le\sum_{i\in S^*}\big(\mathrm{LCB}_{T+1}(i)-\mathrm{LCB}_1(i)\big)+\sum_{t=1}^T\sum_{k=1}^K2\alpha\Delta_{t,k-1}(i_{t,k}).
--   $$
--
--   The lower confidence bounds have telescoped over the periods, so only the boundary terms and the sum of widths remain.
--
--   Differences from the source:
--   - generalization: S* the optimal set → S* any set of K products; reason: the argument does not use optimality; the optimal set is such a set
--   - generalization: α as printed → any α ≥ 0; reason: the argument uses only the sign of α; the printed α is positive
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
--   - reading: d, K, N, T unconstrained on the page → K ≤ N, with d, K and the period index otherwise free; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N, which makes the K selections of a period distinct; the deterministic step uses no other bound
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, First line of the last display of the proof of Theorem 3, p.19

import Definitions.Def_ShrinkingUCB_ConfidenceBounds
import Definitions.Def_ShrinkingUCB_regret

namespace ShrinkingUCB

/-- The first line of the last display of the proof of Theorem 3, p.19 of arXiv:1903.07844v2: on
the event (4),
`R(T) ≤ ∑_{i ∈ S*} (LCB_{T+1}(i) − LCB_1(i)) + ∑_{t=1}^T ∑_{k=1}^K 2α∆_{t,k-1}(i_{t,k})`. -/
theorem regret_le_lcb_sum {d N : ℕ} (K T : ℕ) (hKN : K ≤ N) (I : LinearSemiBandit d N)
    (tb : TieBreak N) {α : ℝ} (hα : 0 ≤ α) (o : OutcomeTable N)
    (Sstar : Finset (Fin N)) (hS : Sstar.card = K) (h4 : ConfidenceHolds I tb α K o T) :
    regret I tb α K Sstar T o ≤
      ∑ i ∈ Sstar, (LCB I tb α K o (T + 1) i - LCB I tb α K o 1 i)
        + ∑ t ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 K,
            2 * α * Delta I tb α K o t (k - 1) (pick I tb α K o t k) := by sorry

end ShrinkingUCB
