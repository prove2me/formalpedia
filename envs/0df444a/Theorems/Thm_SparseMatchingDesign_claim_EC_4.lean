-- Prove2me | Theorems.Thm_SparseMatchingDesign_claim_EC_4
-- name    : SparseMatchingDesign.claim_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:47.141417+00:00
-- url     : https://prove2.me/theorems/6aa6d286-ce23-48d0-b9e7-522f5868b134
-- title:
--   Claim EC.4 — if $X=0$, $\mu(\widetilde R_{n,K})=\mu(\widetilde K_n)$
-- statement:
--   Let $K\ge1$ divide $n$ and let $S$ be the set of surviving nodes. If no residual sub-cluster is empty ($X=0$), then the maximum matching size of the residual $K$-ring equals that of the residual complete graph on the same surviving nodes:
--   $$\mu(\widetilde R_{n,K})=\mu(\widetilde K_n).$$
--   This is the corner case of the proof of Theorem 3.
--
--   Differences from the source:
--   - encoding: R̃_{n,K} and K̃ₙ for the same random surviving set → (kRing n K).induce S and (⊤ : SimpleGraph (Fin n)).induce S for every S; reason: the identity holds pointwise for every realisation
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.4, p.ec8 (pdf p.51)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_emptySubClusterCount

namespace SparseMatchingDesign

/-- **Claim EC.4.** If no residual sub-cluster is empty (`X = 0`), the maximum matching size of
the residual `K`-ring equals that of the residual complete graph on the same surviving nodes:
`μ(R̃_{n,K}) = μ(K̃ₙ)`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.4, p.ec8: "If X = 0, the maximum matching size in R̃_{n,K} is the same as
that in K̃ₙ."

**Formalization Note** Both residual graphs are induced on the same surviving set `S`:
`(kRing n K).induce S` and `(⊤ : SimpleGraph (Fin n)).induce S`. μ is
`TuranMatching.Clique.matchingNumber`. The claim holds for every `S`; `K ≥ 1` and `K ∣ n` are
the paper's standing assumptions (footnote 5, p.19). -/
theorem claim_EC_4 (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (S : Finset (Fin n))
    (hX : emptySubClusterCount K S = 0) :
    TuranMatching.Clique.matchingNumber ((kRing n K).induce (S : Set (Fin n))) =
      TuranMatching.Clique.matchingNumber ((⊤ : SimpleGraph (Fin n)).induce (S : Set (Fin n))) := by sorry

end SparseMatchingDesign
