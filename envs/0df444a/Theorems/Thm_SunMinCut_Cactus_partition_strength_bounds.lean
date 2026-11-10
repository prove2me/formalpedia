-- Prove2me | Theorems.Thm_SunMinCut_Cactus_partition_strength_bounds
-- name    : SunMinCut.Cactus.partition_strength_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:22:39.447688+00:00
-- url     : https://prove2.me/theorems/0cc14dca-335b-48ad-96ee-e4e7ead53c95
-- title:
--   §2.2 display — λ/2 ≤ σ(G) ≤ λ
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices with positive capacities and minimum-cut value $\lambda$. Its partition strength $\sigma(G)=\min_{|P|\ge2}w(\delta P)/(|P|-1)$, the minimum over partitions $P$ of $V$ into at least two blocks of the capacity between blocks divided by the number of blocks minus one, satisfies
--   $$\lambda/2\le\sigma(G)\le\lambda.$$
--
--   Differences from the source: none.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, §2.2 display, p. 8

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph

namespace SunMinCut.Cactus

/-- **The partition-strength bounds**, Sun 2026, doi:10.5281/zenodo.23915020, §2.2 display, p. 8:
for a connected graph on `n ≥ 2` vertices with positive capacities, the partition strength
`σ(G) = min_{|P| ≥ 2} w(δP)/(|P| − 1)` satisfies `λ/2 ≤ σ(G) ≤ λ`. -/
theorem partition_strength_bounds (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) :
    lam G / 2 ≤ sigma G ∧ sigma G ≤ lam G := by sorry

end SunMinCut.Cactus
