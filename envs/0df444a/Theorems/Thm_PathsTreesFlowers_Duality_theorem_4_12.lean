-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_theorem_4_12
-- name    : PathsTreesFlowers.Duality.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:06.64884+00:00
-- url     : https://prove2.me/theorems/433ae93c-59e8-4e89-a3f6-09c766f71116
-- title:
--   4.12, p. 458 — for the blossom B of a flower, M is maximum in G iff M/B is maximum in G/B
-- statement:
--   Let $M$ be a matching of a finite graph $G$, and let $B$ be the blossom of a flower for $(G, M)$: an odd circuit for which $M \cap B$ is a maximum matching of $B$ leaving the vertex $b$ exposed, together with a stem whose tip is $b$ and which meets $B$ only at $b$. Then
--
--   $$M \text{ is a maximum matching of } G \iff M/B \text{ is a maximum matching of } G/B,$$
--
--   where $G/B$ is obtained by shrinking the vertex set of $B$ and $M/B = M \cap (G/B)$.
--
--   This is the key theorem of the blossom algorithm: a blossom found while growing a planted tree can be shrunk without changing whether the current matching is maximum.
--
--   **Formalization Note** The stem is essential: the paper notes (§7.1, p. 465) that "the sufficiency part of (4.12) depends on the blossom being part of a flower".
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 458, 4.12

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Duality

theorem theorem_4_12 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M)
    (vs : List V) (es : List E) (b : V) (svs : List V) (ses : List E)
    (hF : IsFlower G M vs es b svs ses) :
    IsMaxMatching G M ↔
      IsMaxMatching (shrink G (blockPartition vs.toFinset))
        (shrinkMatching G (blockPartition vs.toFinset) M) := by sorry

end PathsTreesFlowers.Duality
