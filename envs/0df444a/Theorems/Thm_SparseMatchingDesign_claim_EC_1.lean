-- Prove2me | Theorems.Thm_SparseMatchingDesign_claim_EC_1
-- name    : SparseMatchingDesign.claim_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:28.164918+00:00
-- url     : https://prove2.me/theorems/9fa42afe-e555-4f7d-beab-5ab087be9ef5
-- title:
--   Claim EC.1 — consecutive non-empty sub-clusters induce a connected chain of sub-clusters
-- statement:
--   Let $K\ge1$ divide $n$, let $S$ be the set of surviving nodes, and let $\widetilde C_r,\widetilde C_{r+1},\dots,\widetilde C_{s}$ be a run of cyclically consecutive residual sub-clusters (indices modulo $n/K$, at most $n/K$ of them) that are all non-empty. Then
--
--   1. the run is a chain of sub-clusters: each $\widetilde C_t$ is a clique of size at most $K$ and every node of $\widetilde C_t$ is adjacent to every node of $\widetilde C_{t+1}$; and
--   2. the subgraph of the residual $K$-ring $\widetilde R_{n,K}$ induced by $\widetilde C_r\cup\dots\cup\widetilde C_s$ is connected.
--
--   Together with Claim EC.2 this describes the components of the residual $K$-ring.
--
--   Differences from the source:
--   - generalization: consecutive sub-clusters r, r + 1, …, s with increasing indices (Claim EC.1); the remark on p.ec7 extends it to runs r, …, n/K, 1, …, s → any run of ℓ cyclically consecutive sub-clusters (r + t) mod (n/K), t < ℓ, 1 ≤ ℓ ≤ n/K, any start r; reason: the increasing runs are the case r + ℓ ≤ n/K, so it specializes to the claim; the wrapping runs are the paper's own remark
--   - encoding: the subgraph of R̃_{n,K} induced by C̃_r ∪ … ∪ C̃_s → (kRing n K).induce of the run's union; reason: an induced subgraph of an induced subgraph is the induced subgraph on the smaller set; same graph
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.1, p.ec6 (pdf p.49), and the remark after its proof, p.ec7 (pdf p.50)

import Mathlib
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_subCluster
import Definitions.Def_SparseMatchingDesign_runUnion
import Definitions.Def_SparseMatchingDesign_IsChainOfSubClusters

namespace SparseMatchingDesign

/-- **Claim EC.1.** If the residual sub-clusters `C̃_r, C̃_{r+1}, …, C̃_s` of a run of cyclically
consecutive sub-clusters are all non-empty, then the subgraph of the residual `K`-ring induced by
`C̃_r ∪ … ∪ C̃_s` is a chain of sub-clusters `r, …, s`, and it is connected.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.1, p.ec6: "Let C̃_r, C̃_{r+1}, …, C̃_s be consecutive, non-empty sets of nodes
in sub-clusters r, r + 1, …, and s, respectively. Then, the subgraph of R̃_{n,K} induced by the
node set C̃_r ∪ C̃_{r+1} ∪ … ∪ C̃_s is a chain of sub-clusters r, r + 1, …, and s in the sense
described above. Furthermore, the induced subgraph is connected." Remark after the proof, p.ec7:
"If C̃_r, …, C̃_{n/K}, C̃_1, …, C̃_s are all non-empty, then Claim EC.1 also applies to this sequence
of node sets, because sub-clusters n/K and 1 are adjacent in R̃_{n,K} as well."

**Formalization Note** The run is `ℓ` sub-clusters `(r + t) mod (n/K)`, `t < ℓ`, with
`1 ≤ ℓ ≤ n/K` (0-based indices), covering the increasing runs of the claim and the wrapping runs
of the remark. The subgraph of `R̃_{n,K} = (kRing n K).induce S` induced by a subset of `S` is
`(kRing n K).induce` of that subset. `K ≥ 1` and `K ∣ n` are the paper's standing assumptions
(footnote 5, p.19). -/
theorem claim_EC_1 (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (S : Finset (Fin n)) (r ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hℓm : ℓ ≤ n / K)
    (hne : ∀ t < ℓ, (subCluster K S ((r + t) % (n / K))).Nonempty) :
    IsChainOfSubClusters K S r ℓ ∧
    ((kRing n K).induce (runUnion K S r ℓ : Set (Fin n))).Connected := by sorry

end SparseMatchingDesign
