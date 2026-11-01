-- Prove2me | Theorems.Thm_ShrinkingUCB_delta_antitone
-- name    : ShrinkingUCB.delta_antitone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:04.796192+00:00
-- url     : https://prove2.me/theorems/147f550e-633a-4a8d-bda6-17baa9c791ed
-- title:
--   Display after step ⑤, p.17 — $\Delta_{t+1,0}(i)\le\Delta_{t,k-1}(i)$
-- statement:
--   Let $K\le N$. On every outcome table, for every period $t\ge1$, every $k\in[K]$ and every product $i$,
--
--   $$
--   \Delta_{t+1,0}(i)\le\Delta_{t,k-1}(i).
--   $$
--
--   Widths can only shrink as the design matrix grows, within a period and across periods.
--
--   Differences from the source:
--   - encoding: √(x⊤A_t⁻¹x_i), √(x⊤A_{t,K}⁻¹x_i) in the display → x_i on both sides; reason: the page drops the subscript twice; the outer terms are ∆ of x_i
--   - generalization: α as printed → any real α; reason: the claim concerns the matrices of any run
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
--   - reading: d, K, N, T unconstrained on the page → K ≤ N, with d, K and the period index otherwise free; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N, which makes the K selections of a period distinct; the deterministic step uses no other bound
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Step ⑤ of the proof of Proposition 1, p.17

import Definitions.Def_ShrinkingUCB_ConfidenceBounds

namespace ShrinkingUCB

/-- The display after step ⑤, p.17 of arXiv:1903.07844v2:
`∆_{t+1,0}(i) ≤ ∆_{t,k-1}(i)` for every `k ∈ [K]`, on every outcome table.

**Formalization Note.** `K ≤ N` makes the `K` selections of a period distinct, so that
`A_t = A_{t,K}`. -/
theorem delta_antitone {d N : ℕ} (K : ℕ) (hKN : K ≤ N) (I : LinearSemiBandit d N)
    (tb : TieBreak N) (α : ℝ) (o : OutcomeTable N) (t : ℕ) (ht : 1 ≤ t)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 K) (i : Fin N) :
    Delta I tb α K o (t + 1) 0 i ≤ Delta I tb α K o t (k - 1) i := by sorry

end ShrinkingUCB
