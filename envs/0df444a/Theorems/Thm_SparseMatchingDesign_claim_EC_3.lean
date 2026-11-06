-- Prove2me | Theorems.Thm_SparseMatchingDesign_claim_EC_3
-- name    : SparseMatchingDesign.claim_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:53.649295+00:00
-- url     : https://prove2.me/theorems/aee4ddad-e352-48ea-ae1e-5c3f10a935d3
-- title:
--   Claim EC.3 — if $X>0$, at most $X$ nodes are unmatched in a maximum matching of $\widetilde R_{n,K}$
-- statement:
--   Let $K\ge1$ divide $n$ and let $S$ be the set of surviving nodes. If $X>0$, then at most $X$ surviving nodes are unmatched in a maximum matching of the residual $K$-ring:
--   $$|S|\le 2\,\mu(\widetilde R_{n,K})+X.$$
--   With Claim EC.4 this bounds the loss pointwise by $X$.
--
--   Differences from the source:
--   - encoding: at most X nodes are unmatched in a maximum matching of R̃_{n,K} → S.card ≤ 2 * μ((kRing n K).induce S) + X; reason: a maximum matching has μ edges and leaves |S| − 2μ surviving nodes unmatched; written without ℕ subtraction
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.3, p.ec8 (pdf p.51)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_emptySubClusterCount

namespace SparseMatchingDesign

/-- **Claim EC.3.** If at least one residual sub-cluster is empty (`X > 0`), then at most `X`
surviving nodes are unmatched in a maximum matching of the residual `K`-ring:
`|Ṽ| − 2 μ(R̃_{n,K}) ≤ X`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, Claim EC.3, p.ec8: "If X > 0, then at most X nodes are unmatched in a maximum
matching of R̃_{n,K}."

**Formalization Note** A maximum matching of `R̃_{n,K} = (kRing n K).induce S` has
`μ = TuranMatching.Clique.matchingNumber` edges and leaves `|S| − 2μ` surviving nodes unmatched;
the claim is written `|S| ≤ 2μ + X` to avoid natural-number subtraction. It holds for every
surviving set `S`; `K ≥ 1` and `K ∣ n` are the paper's standing assumptions (footnote 5,
p.19). -/
theorem claim_EC_3 (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (S : Finset (Fin n))
    (hX : 0 < emptySubClusterCount K S) :
    S.card ≤ 2 * TuranMatching.Clique.matchingNumber ((kRing n K).induce (S : Set (Fin n))) +
      emptySubClusterCount K S := by sorry

end SparseMatchingDesign
