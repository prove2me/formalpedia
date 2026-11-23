-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_Supplement_augmenting_tree_4_4
-- name    : PathsTreesFlowers.Duality.Supplement.augmenting_tree_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:39:01.600268+00:00
-- url     : https://prove2.me/theorems/40a1a464-053b-4b7e-ab1d-dbfaad093d53
-- title:
--   4.4 — The root-to-new-exposed-vertex path of every augmenting tree is augmenting
-- statement:
--   Let $J$ be a planted tree for a matching $M$, with root $r$. Adjoin an edge $e$ from an outer vertex $u$ to an exposed vertex $v$ outside $J$, forming $J_A$. The unique path in this actual enlarged subgraph from $r$ to $v$ is augmenting:
--   $$P\text{ alternates for }M,\qquad |E(P)|>0,\qquad r,v\text{ are exposed for }M.$$
--
--   Both the existence and uniqueness of the oriented path are explicit. This includes the case where $J$ is a singleton and the augmenting path consists only of $e$.
--
--   Differences from the source:
--   - encoding: the path in J_A joining v₂ to the root → a unique oriented root-to-new-vertex path in the subgraph obtained by adjoining the specified edge and its endpoints; reason: 4.0 gives uniqueness; reversing orientation gives the same source path
--   - encoding: an augmenting path → an alternating path of positive length with both endpoints exposed; reason: 3.6 defines augmentation this way, and the outside-J condition makes the endpoints distinct
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 455, 4.4

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem augmenting_tree_4_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V) (e : E) (u v : V)
    (hA : IsAugmentingTree G M J r e u v) :
    ∃ vs es, PathIn G (adjoinEdge G J.toSub e u v hA.2.2.2.2) r v vs es ∧
      (∀ ws fs, PathIn G (adjoinEdge G J.toSub e u v hA.2.2.2.2) r v ws fs →
        ws = vs ∧ fs = es) ∧
      IsAlternatingPath G M vs es ∧ 0 < es.length ∧
      IsExposed G M r ∧ IsExposed G M v := by sorry

end PathsTreesFlowers.Duality.Supplement
