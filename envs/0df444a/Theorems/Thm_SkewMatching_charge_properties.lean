-- Prove2me | Theorems.Thm_SkewMatching_charge_properties
-- name    : SkewMatching.charge_properties
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:39.310057+00:00
-- url     : https://prove2.me/theorems/bb7c493a-41ef-47ae-b4ad-d8b0ee8be4c9
-- title:
--   §3.2, p.6 and Appendix A, p.15 — charges are symmetric, in {−2,…,2}, and negative edges violate the barrier
-- statement:
--   Let $(A,A',X_1,\dots,X_k,M)$ be a barrier of a sub-multigraph $H$ of a finite skew-symmetric graph $G$, let $K$ be a parameter, and let $e$ be any edge of $G$. Then
--
--   $$
--   d_{\sigma(e)}=d_e,\qquad -2\le d_e\le 2,
--   $$
--
--   and if $d_e<0$ then the pair $\{e,\sigma(e)\}$ violates the barrier: the partition is not a barrier of $H\cup\{e,\sigma(e)\}$.
--
--   So a sampled negative edge is real progress for the search, and the charges can be used as a sampling weight.
--
--   Differences from the source:
--   - generalization: K a parameter, positive throughout the paper → K any natural number; reason: at K = 0 every fragment is small and the same table applies; K ≥ 1 is the printed case
--   - generalization: active edges of the residual graph → every edge of a finite SkewGraph G with a σ-closed H; reason: G.doubled with H inside the active edges is the printed case; the claim does not use activity
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.2, p.6; Appendix A, p.15

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_charge

namespace SkewMatching

/-- **Charges**, §3.2, p.6, with Appendix A, p.15. "This edge charge has the following properties. First, charges d_e are symmetric and in the range {−2, −1, 0, 1, 2}. Second, negatively charged edges can be added to the subgraph H to bypass the
barrier." Appendix A: "every edge with negative charge in Definition 12 violates the barrier that defines the charges."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.2, p.6; Appendix A, p.15.

**Formalization Note.** `H` is a sub-multigraph of `G`, the barrier is on `H` and the charges are on all edges of `G`. `K` is any natural number. -/
theorem charge_properties {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (H : Finset E)
    (hH : G.SymmClosed H) (s : V) (P : Partition V) (hP : G.IsBarrier H s P) (K : ℕ) (e : E) :
    G.charge K H P (G.σE e) = G.charge K H P e ∧
      -2 ≤ G.charge K H P e ∧ G.charge K H P e ≤ 2 ∧
        (G.charge K H P e < 0 → G.Violates H s P e) := by sorry

end SkewMatching
