-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_berge_3_7
-- name    : PathsTreesFlowers.Duality.berge_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:02.028416+00:00
-- url     : https://prove2.me/theorems/40917f19-88ab-4f5f-b9f2-e670ef1bccf7
-- title:
--   3.7 (Berge), p. 453 — M is not maximum iff (G, M) contains an alternating path joining two exposed vertices
-- statement:
--   Let $M$ be a matching in a finite graph $G$. Then $M$ is not of maximum cardinality if and only if there is an alternating path in $(G, M)$ with at least one edge whose two end-points are both exposed for $M$:
--
--   $$M \text{ not maximum} \iff \exists\, v_0 e_0 v_1 \cdots e_{m-1} v_m \text{ alternating},\ m \ge 1,\ v_0, v_m \text{ exposed}.$$
--
--   Such a path is *augmenting* (3.6): exchanging its edges in and out of $M$ yields a matching larger by one. This is Berge's characterization of maximum matchings, the basis of every augmenting-path algorithm.
--
--   **Formalization Note** "An alternating path joining two exposed vertices" requires at least one edge (two distinct end-points). A one-vertex path joins its vertex to itself (3.3), and an exposed vertex alone would make the statement false.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 453, 3.7 (Berge, 1)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Duality

theorem berge_3_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M) :
    ¬ IsMaxMatching G M ↔
      ∃ (vs : List V) (es : List E), IsAlternatingPath G M vs es ∧ es ≠ [] ∧
        (∀ a ∈ vs.head?, IsExposed G M a) ∧ (∀ b ∈ vs.getLast?, IsExposed G M b) := by sorry

end PathsTreesFlowers.Duality
