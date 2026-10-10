-- Prove2me | Theorems.Thm_TaitTobin_Planar_planar_facts
-- name    : TaitTobin.Planar.planar_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:48:23.713359+00:00
-- url     : https://prove2.me/theorems/12c42b90-43bc-403c-8291-6de3edff1dee
-- title:
--   §3, p. 8 — a planar graph has no K₃,₃, at most 3n − 6 edges, and bipartite subgraphs with at most 2n − 4 edges
-- statement:
--   Let $G$ be a planar graph on $n \ge 3$ vertices. Then
--
--   1. $G$ contains no subgraph isomorphic to $K_{3,3}$;
--   2. $G$ has at most $3n - 6$ edges;
--   3. every bipartite subgraph $H$ of $G$ has at most $2n - 4$ edges:
--   $$|E(G)| \le 3n - 6, \qquad |E(H)| \le 2n - 4 \quad (H \subseteq G \text{ bipartite}).$$
--
--   These are the three planarity facts that the proof of Theorem 15 uses throughout.
--
--   **Formalization Note** Planarity is the published topological notion (a crossing-free arc drawing). The hypothesis $n \ge 3$ is needed for the two edge counts ($K_2$ has $1 > 3\cdot 2 - 6$ edges) and makes the natural-number subtractions exact. "No $K_{3,3}$ subgraph" is `Free`, the absence of an injective homomorphism from $K_{3,3}$. A bipartite subgraph is a subgraph $H \le G$ on the same vertex set that is properly 2-colorable; isolated vertices do not change its edge count.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 8, §3, "We will use frequently that G has no K_{3,3} as a subgraph, that m ≤ 3n − 6, and that any bipartite subgraph of G has at most 2n − 4 edges."

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- §3, p. 8: a planar graph on `n ≥ 3` vertices contains no copy of `K₃,₃`, has at most
`3n - 6` edges, and every bipartite subgraph of it has at most `2n - 4` edges. -/
theorem planar_facts {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsPlanar G) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free G ∧
      G.edgeFinset.card ≤ 3 * n - 6 ∧
      ∀ H : SimpleGraph (Fin n), H ≤ G → H.Colorable 2 → H.edgeFinset.card ≤ 2 * n - 4 := by sorry
end TaitTobin.Planar
