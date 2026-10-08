-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_15
-- name    : PathsTreesFlowers.Duality.lemma_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:00.726181+00:00
-- url     : https://prove2.me/theorems/2323991a-f2cd-4633-a9ce-56862a1d58ba
-- title:
--   4.15, p. 458 — if M ∩ P leaves one exposed vertex, M/P is maximum in G/P and P/P is the tip of a stem, then M is maximum
-- statement:
--   Let $M$ be a matching of a finite graph $G$ and $U$ a set of vertices whose induced subgraph $U^+$ is connected; write $G/U$ for the graph obtained by shrinking $U$ and $M/U = M \cap (G/U)$. Suppose that
--
--   1. exactly one vertex of $U$ meets no edge of $M$ with both end-points in $U$;
--   2. $M/U$ is a maximum matching of $G/U$;
--   3. the vertex $U/U$ is the tip of a stem for $(G/U, M/U)$ (possibly a stem with no edges, i.e. $U/U$ exposed for $M/U$).
--
--   Then $M$ is a maximum matching of $G$.
--
--   Together with 4.14 this gives 4.12, and its extension to several disjoint shrunken sets is the step of the algorithm that certifies maximality.
--
--   **Formalization Note** The paper states 4.15 for a connected subgraph $P$ with $M \cap P$ leaving exactly one exposed vertex in $P$. Shrinking depends only on the vertex set $U$ of $P$ (4.9), and if (1) holds for $P$ it holds for $U^+$ (the matching $M \cap U^+$ contains $M \cap P$ and $|U|$ is odd), so this statement implies the paper's. Connectedness of $U^+$ is the standing assumption under which 4.9 defines shrinking.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 458, 4.15

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Duality

theorem lemma_4_15 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (U : Finset V)
    (hconn : IsConnectedSub G (induced G U))
    (h1 : (exposedIn G U M).card = 1)
    (h2 : IsMaxMatching (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M))
    (h3 : ∃ (svs : List {W : Finset V // W ∈ (blockPartition U).parts})
        (ses : List {e : E // ¬ InsidePart G (blockPartition U) e}),
        IsStem (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M) svs ses ∧
          ∃ u ∈ U, svs.getLast? = some (toPart (blockPartition U) u)) :
    IsMaxMatching G M := by sorry

end PathsTreesFlowers.Duality
