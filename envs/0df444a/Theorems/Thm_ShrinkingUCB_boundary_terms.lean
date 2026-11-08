-- Prove2me | Theorems.Thm_ShrinkingUCB_boundary_terms
-- name    : ShrinkingUCB.boundary_terms
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:20:25.880894+00:00
-- url     : https://prove2.me/theorems/85e4f3dc-2fe2-4099-829a-d71b13dd15b7
-- title:
--   Boundary terms, p.19 — $\sum_{S^*}\mathrm{LCB}_{T+1}\le K$ and $\sum_{S^*}-\mathrm{LCB}_1\le\alpha K$
-- statement:
--   Let $\alpha\ge0$ and $|S^*|=K$. On every outcome table on which (4) holds,
--
--   $$
--   \sum_{i\in S^*}\mathrm{LCB}_{T+1}(i)\le K,
--   $$
--
--   and on every outcome table,
--
--   $$
--   \sum_{i\in S^*}-\mathrm{LCB}_1(i)\le\alpha K.
--   $$
--
--   These two bounds give the fixed cost $K+\alpha K$ of the regret bound, which does not depend on $T$.
--
--   Differences from the source:
--   - generalization: S* the optimal set → S* any set of K products; reason: the argument does not use optimality; the optimal set is such a set
--   - generalization: α as printed → any α ≥ 0; reason: the argument uses only the sign of α; the printed α is positive
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Boundary terms in the proof of Theorem 3, p.19

import Definitions.Def_ShrinkingUCB_ConfidenceBounds

namespace ShrinkingUCB

/-- The boundary terms, p.19 of arXiv:1903.07844v2: on the event (4),
`∑_{i ∈ S*} LCB_{T+1}(i) ≤ K`; and on every outcome table, `∑_{i ∈ S*} −LCB_1(i) ≤ αK`. -/
theorem boundary_terms {d N : ℕ} (K T : ℕ) (I : LinearSemiBandit d N)
    (tb : TieBreak N) {α : ℝ} (hα : 0 ≤ α) (o : OutcomeTable N)
    (Sstar : Finset (Fin N)) (hS : Sstar.card = K) :
    (ConfidenceHolds I tb α K o T → ∑ i ∈ Sstar, LCB I tb α K o (T + 1) i ≤ K) ∧
    ∑ i ∈ Sstar, -LCB I tb α K o 1 i ≤ α * K := by sorry

end ShrinkingUCB
