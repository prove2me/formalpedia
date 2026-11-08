-- Prove2me | Theorems.Thm_SkewMatching_lemma_15
-- name    : SkewMatching.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:08.541249+00:00
-- url     : https://prove2.me/theorems/f3bd2cbe-ddb8-466e-87fe-9d4e9d6cd081
-- title:
--   Lemma 15 — the total charge on a flow of value at least K/2 is negative
-- statement:
--   Let $G$ be a finite skew-symmetric graph, let $d$ be the charges of a barrier on a sub-multigraph $H$ of $G$ with a parameter $K\ge 1$, and let $f$ be an integral symmetric flow in $G$ with $|f|\ge K/2$. Then
--
--   $$
--   \sum_e f_e d_e<0.
--   $$
--
--   This is the balance condition of the algorithm: in the residual graph, the remaining flow is charged negatively, so the expected change of the variables along it is negative. Note that the barrier is on the subgraph while the flow is on the whole graph, so the edges of $G$ may cross the barrier.
--
--   Differences from the source:
--   - generalization: G the current residual graph → every finite SkewGraph G; reason: the proof uses no property of residual graphs; G.doubled with a flow on active edges gives the printed case
--   - encoding: a parameter K → K a natural number with K ≥ 1; reason: K is a positive integer in the paper; with no large fragment the bound −2|f| < 0 needs |f| > 0
--   - encoding: value at least K/2 → K ≤ 2·value; reason: the same condition without division
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 15, p.9

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_IsFlow
import Definitions.Def_SkewMatching_SkewGraph_charge

namespace SkewMatching

/-- **Lemma 15**, p.9. "Let G be the current residual graph, and d be an operation vector based on a barrier on a subgraph of G. For an integral symmetric flow f in G of value at least K/2, the total charge on edges in the flow is negative, i.e., Σ_e f_e d_e < 0."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 15, p.9.

**Formalization Note.** For every finite `SkewGraph` `G`, multigraphs included, since the proof uses no simplicity. To apply this to the residual graph of a flow, take `G.doubled` with a flow supported on active edges. `K ≥ 1`: with no large fragment the bound is `−2|f| < 0`, which needs
`|f| > 0`, and `K` is a positive parameter throughout the paper ("2n/K"). `K/2 ≤ |f|` is written `K ≤ 2 |f|`. -/
theorem lemma_15 {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (H : Finset E)
    (hH : G.SymmClosed H) (s : V) (P : Partition V) (hP : G.IsBarrier H s P) (K : ℕ) (hK : 1 ≤ K)
    (f : E → ℕ) (hf : G.IsFlow s f) (hv : (K : ℤ) ≤ 2 * G.value s f) :
    ∑ e, (f e : ℤ) * G.charge K H P e < 0 := by sorry

end SkewMatching
