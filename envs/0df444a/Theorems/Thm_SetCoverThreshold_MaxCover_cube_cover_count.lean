-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_cube_cover_count
-- name    : SetCoverThreshold.MaxCover.cube_cover_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:05:09.385751+00:00
-- url     : https://prove2.me/theorems/d0e170e3-03b1-4887-a4b5-a32a5ca18dfc
-- title:
--   Coverage count of the explicit partition system $\{0,\dots,k-1\}^L$ (proof of Theorem 5.3)
-- statement:
--   Let $k\ge1$ and let $\iota$ be a finite index set of size $L$. Consider the partition system whose points are the vectors $x\in\{0,\dots,k-1\}^{\iota}$ ($m=k^L$ points) and whose $i$th partition splits the points into $k$ subsets according to the value $x_i$. Take $j$ subsets from $j$ pairwise different partitions: for a set $J\subseteq\iota$ with $|J|=j$ and values $v_i$ ($i\in J$), the subsets $\{x : x_i=v_i\}$. Then their union has exactly
--   $$\big(1-(1-1/k)^j\big)\,m$$
--   points.
--
--   This exact count, for sets from pairwise different partitions, is what replaces property (4) of partition systems in the max $k$-cover reduction; the concavity of $j\mapsto(1-(1-1/k)^j)m$ drives Proposition 5.4.
--
--   **Formalization Note** The paper's "pairwise disjoint partitions" means pairwise different partitions, which is the condition that each $i\in J$ contributes one subset.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 649, proof of Theorem 5.3 (explicit partition systems)

import Mathlib
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

/-- **The explicit partition system of §5** (Feige 1998, p. 649, proof of Theorem 5.3): in the
partition system on `{0, …, k − 1}^ι` whose `i`th partition splits the points by their
`i`th coordinate, any `j` subsets taken from `j` pairwise different partitions (the subset
with value `v i` of partition `i`, for `i ∈ J`, `|J| = j`) cover exactly
`(1 − (1 − 1/k)^j) · k^{|ι|}` points. -/
theorem cube_cover_count (k : ℕ) (hk : 1 ≤ k) (ι : Type) [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (v : ι → Fin k) :
    ((Finset.univ.filter (fun x : ι → Fin k => ∃ i ∈ J, cubeSystem k ι x i = v i)).card : ℝ) =
      (1 - (1 - 1 / (k : ℝ)) ^ J.card) * (k : ℝ) ^ Fintype.card ι := by sorry

end SetCoverThreshold.MaxCover
