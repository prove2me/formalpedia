-- Prove2me | Theorems.Thm_SparseMatchingDesign_claim_EC_2
-- name    : SparseMatchingDesign.claim_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:44.343664+00:00
-- url     : https://prove2.me/theorems/96cb1c6f-0cc3-4c84-bb0b-d4089339522f
-- title:
--   Claim EC.2 — if $X>0$, $\widetilde R_{n,K}$ has at most $X$ components, each a chain of sub-clusters
-- statement:
--   Let $K\ge1$ divide $n$ and let $S$ be the set of surviving nodes. If at least one residual sub-cluster is empty ($X>0$), then
--
--   1. the residual $K$-ring $\widetilde R_{n,K}$ has at most $X$ connected components, and
--   2. each connected component is a chain of sub-clusters: its node set is $\widetilde C_r\cup\dots\cup\widetilde C_{r+\ell-1}$ for a run of cyclically consecutive non-empty sub-clusters whose neighbouring sub-clusters $\widetilde C_{r-1}$ and $\widetilde C_{r+\ell}$ are empty, and that run is a chain of sub-clusters.
--
--   Each component therefore leaves at most one node unmatched, which is used in Claim EC.3.
--
--   Differences from the source:
--   - generalization: each connected component is a chain of sub-clusters → each component's node set is the union of a run of non-empty sub-clusters whose two neighbouring sub-clusters are empty, and the run is a chain of sub-clusters; reason: maximality of the run is implied (a non-empty sub-cluster next to the run is linked to it and lies in the same component), so the statement specializes to the claim
--   - encoding: connected components of R̃_{n,K} → Nat.card of the ConnectedComponent type of (kRing n K).induce S on the subtype of S; reason: deleted nodes are not vertices of the residual graph; the vertex type is finite, so Nat.card is the number of components
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.2, p.ec7 (pdf p.50)

import Mathlib
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_subCluster
import Definitions.Def_SparseMatchingDesign_emptySubClusterCount
import Definitions.Def_SparseMatchingDesign_runUnion
import Definitions.Def_SparseMatchingDesign_IsChainOfSubClusters

namespace SparseMatchingDesign

/-- **Claim EC.2.** If at least one residual sub-cluster is empty (`X > 0`), then the residual
`K`-ring `R̃_{n,K}` has at most `X` connected components, and each connected component is a
chain of sub-clusters: its node set is the union of a maximal run of cyclically consecutive
non-empty residual sub-clusters, and that run is a chain of sub-clusters.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.2, p.ec7: "If X > 0, then there are at most X connected components in
R̃_{n,K}. Furthermore, each connected component is a chain of sub-clusters."

**Formalization Note** `R̃_{n,K}` is `(kRing n K).induce S` on the vertex type `↥S` (deleted nodes
are not vertices), and the number of its components is `Nat.card` of its `ConnectedComponent`
type. A run is `ℓ` sub-clusters `(r + t) mod (n/K)`, `t < ℓ` (0-based); maximality is that the
sub-clusters right after (`r + ℓ`) and right before (`r + n/K − 1`) the run are empty. The claim
holds for every surviving set `S`; `K ≥ 1` and `K ∣ n` are the paper's standing assumptions
(footnote 5, p.19). -/
theorem claim_EC_2 (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (S : Finset (Fin n))
    (hX : 0 < emptySubClusterCount K S) :
    Nat.card ((kRing n K).induce (S : Set (Fin n))).ConnectedComponent ≤
        emptySubClusterCount K S ∧
    ∀ c : ((kRing n K).induce (S : Set (Fin n))).ConnectedComponent,
      ∃ r ℓ : ℕ, r < n / K ∧ 1 ≤ ℓ ∧ ℓ < n / K ∧
        (∀ t < ℓ, (subCluster K S ((r + t) % (n / K))).Nonempty) ∧
        subCluster K S ((r + ℓ) % (n / K)) = ∅ ∧
        subCluster K S ((r + n / K - 1) % (n / K)) = ∅ ∧
        (∀ v : (S : Set (Fin n)), v ∈ c.supp ↔ (v : Fin n) ∈ runUnion K S r ℓ) ∧
        IsChainOfSubClusters K S r ℓ := by sorry

end SparseMatchingDesign
