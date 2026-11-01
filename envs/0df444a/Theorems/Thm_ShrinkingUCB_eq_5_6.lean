-- Prove2me | Theorems.Thm_ShrinkingUCB_eq_5_6
-- name    : ShrinkingUCB.eq_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:04.79288+00:00
-- url     : https://prove2.me/theorems/59fef350-763b-42c5-b827-c6b3c5a50a95
-- title:
--   Eqs. (5)–(6), p.17 — the per-selection inequalities on the event (4)
-- statement:
--   Let $K\le N$, $\alpha\ge0$, and consider an outcome table on which (4) holds for $T$. Let $S^*$ be a set of products, $t\in[T]$ and $k\in[K]$.
--
--   1. If $i_{t,k}\notin S^*$, then for all $i^*\in S^*\setminus S_t$,
--   $$
--   \mu(i^*)-\mu(i_{t,k})\le\mathrm{LCB}_{t+1}(i^*)-\mathrm{LCB}_t(i^*)+2\alpha\Delta_{t,k-1}(i_{t,k}).
--   $$
--   2. If $i_{t,k}\in S^*$, then
--   $$
--   0\le\mathrm{LCB}_{t+1}(i_{t,k})-\mathrm{LCB}_t(i_{t,k})+2\alpha\Delta_{t,k-1}(i_{t,k}).
--   $$
--
--   These are the deterministic core of Proposition 1: each selection is charged to the increase of a lower confidence bound plus a width.
--
--   Differences from the source:
--   - reading: S_t in the conditions, ∆_{t,k} "for all k ∈ [K]" → S_t is the final set of period t; ∆_{t,k} for k ∈ {0, …, K}; reason: the proof's step ③ needs i* never picked in period t, and the text uses k = 0 (p.16, p.17)
--   - generalization: S* the optimal set → S* any set of products; reason: the argument does not use optimality or size; the optimal set is such a set
--   - generalization: α as printed → any α ≥ 0; reason: the argument uses only the sign of α; the printed α is positive
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
--   - reading: d, K, N, T unconstrained on the page → K ≤ N, with d, K and the period index otherwise free; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N, which makes the K selections of a period distinct; the deterministic step uses no other bound
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Eqs. (5), (6), p.17

import Definitions.Def_ShrinkingUCB_ConfidenceBounds

namespace ShrinkingUCB

/-- Inequalities (5) and (6), p.17 of arXiv:1903.07844v2: on the event (4), for every selection
`i_{t,k}`, `t ∈ [T]`, `k ∈ [K]`: if `i_{t,k} ∉ S*` then for all `i* ∈ S* \ S_t`,
`µ(i*) − µ(i_{t,k}) ≤ LCB_{t+1}(i*) − LCB_t(i*) + 2α∆_{t,k-1}(i_{t,k})`; and if `i_{t,k} ∈ S*`
then `0 ≤ LCB_{t+1}(i_{t,k}) − LCB_t(i_{t,k}) + 2α∆_{t,k-1}(i_{t,k})`.

**Formalization Note.** `S_t` is the final set of period `t`. `S*` is any set of products, and
`α` any nonnegative parameter. -/
theorem eq_5_6 {d N : ℕ} (K T : ℕ) (hKN : K ≤ N) (I : LinearSemiBandit d N)
    (tb : TieBreak N) {α : ℝ} (hα : 0 ≤ α) (o : OutcomeTable N)
    (Sstar : Finset (Fin N)) (h4 : ConfidenceHolds I tb α K o T)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T) (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
    (pick I tb α K o t k ∉ Sstar →
      ∀ istar ∈ Sstar \ offered I tb α K o t,
        I.μ istar - I.μ (pick I tb α K o t k) ≤
          LCB I tb α K o (t + 1) istar - LCB I tb α K o t istar
            + 2 * α * Delta I tb α K o t (k - 1) (pick I tb α K o t k)) ∧
    (pick I tb α K o t k ∈ Sstar →
      0 ≤ LCB I tb α K o (t + 1) (pick I tb α K o t k) - LCB I tb α K o t (pick I tb α K o t k)
        + 2 * α * Delta I tb α K o t (k - 1) (pick I tb α K o t k)) := by sorry

end ShrinkingUCB
