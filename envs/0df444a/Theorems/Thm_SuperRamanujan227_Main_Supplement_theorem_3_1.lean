-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_theorem_3_1
-- name    : SuperRamanujan227.Main.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:46:32.909563+00:00
-- url     : https://prove2.me/theorems/1c7265d1-c3da-4d6d-a369-e49529da108b
-- title:
--   Theorem 3.1 — One-sided advantage (d−2)/(n−1)
-- statement:
--   For every even integer $n$ and every integer $3\le d<n$, there exists a $d$-regular undirected multigraph $G$ on $n$ vertices such that
--
--   $$\lambda_2(G)\le2\sqrt{d-1}-\frac{d-2}{n-1}.$$
--
--   Here $\lambda_2$ is the second-largest adjacency eigenvalue counted with multiplicity. Parallel edges and loops counted twice are allowed. This is the separate one-sided existence companion theorem; it imposes no bipartiteness or simplicity condition.
--
--   Differences from the source: none.
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 10, Theorem 3.1

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Multigraph

namespace SuperRamanujan227.Main.Supplement

/-- Theorem 3.1, p.10. One-sided graph existence, with no bipartite restriction. -/
theorem theorem_3_1 (n d : ℕ) (hn : Even n) (hd : 3 ≤ d) (hdn : d < n) :
    ∃ G : Multigraph n, G.IsRegular d ∧
      G.eig 2 ≤ 2 * Real.sqrt ((d : ℝ) - 1) - ((d : ℝ) - 2) / ((n : ℝ) - 1) := by sorry

end SuperRamanujan227.Main.Supplement
