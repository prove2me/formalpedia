-- Prove2me | Theorems.Thm_SparseMatchingDesign_ring_density_eq_min
-- name    : SparseMatchingDesign.ring_density_eq_min
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:16:30.757288+00:00
-- url     : https://prove2.me/theorems/5d4bd5ae-31d1-4dab-a04c-7bf7a3bcba96
-- title:
--   p.5 — $R_{n,K}$ is regular of degree $\min\{3K-1,n-1\}$, so $d(R_{n,K})=\min\{3K-1,n-1\}$
-- statement:
--   Let $K\ge1$ divide $n\ge1$. Every node of the $K$-ring $R_{n,K}$ has exactly $\min\{3K-1,\,n-1\}$ neighbours, and hence
--   $$d(R_{n,K})=\min\{3K-1,\;n-1\}.$$
--   When $n/K\ge3$ this is the value $d=3K-1$ used in Theorem 3; when $n/K\le2$ the $K$-ring is the complete graph $K_n$.
--
--   Differences from the source:
--   - reading: the p.5 sentence states regularity and densities of four designs (G_{n,K}, R_{n,K}, C_{n,K}, ER_{n,α}) → the R_{n,K} clauses only (regularity of R_{n,K} and d(R_{n,K}) = min{3K − 1, n − 1}); reason: this milestone is the K-ring fact the mission's goal uses; the other clauses concern other graph designs, which are outside this mission
--   - encoding: R_{n,K} is regular and d(R_{n,K}) = min{3K − 1, n − 1} → every node has min{3K − 1, n − 1} neighbours, and density (kRing n K) = min{3K − 1, n − 1}; reason: the common degree of a regular graph equals its density, so the two clauses say the same; both are stated
--   - encoding: a graph of size n ∈ ℕ, density with |G| in the denominator → hypothesis 0 < n; reason: the density of the graph with no nodes is undefined (0/0)
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §2.1, p.5, display after the list of graph classes (pdf p.5)

import Mathlib
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_density

namespace SparseMatchingDesign

/-- The `K`-ring `R_{n,K}` is regular of degree `min{3K − 1, n − 1}`, so its density is
`d(R_{n,K}) = min{3K − 1, n − 1}`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §2.1, p.5: "It is worth noticing that G_{n,K}, R_{n,K} and C_{n,K} are all regular graphs
while ER_{n,α} is regular in expectation. Also, note that d(G_{n,K}) = K − 1,
d(R_{n,K}) = min{3K − 1, n − 1}, d(C_{n,K}) = min{2K, n − 1}, and E[d(ER_{n,α})] = (n − 1)α."

**Formalization Note** Only the `R_{n,K}` clauses are stated (the other clauses concern other
designs). `K ≥ 1`, `K ∣ n` (§2.1, n = Km; footnote 5, p.19) and `n ≥ 1` (a graph of size n ∈ ℕ
with a density |G| in the denominator) are hypotheses. The degree is `(neighborSet v).ncard`;
`3K − 1` and `n − 1` are natural-number subtractions, exact under these hypotheses. -/
theorem ring_density_eq_min (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (hn : 0 < n) :
    (∀ v : Fin n, ((kRing n K).neighborSet v).ncard = min (3 * K - 1) (n - 1)) ∧
    density (kRing n K) = ((min (3 * K - 1) (n - 1) : ℕ) : ℝ) := by sorry

end SparseMatchingDesign
