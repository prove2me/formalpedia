-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_theorem_4_17
-- name    : PathsTreesFlowers.Duality.theorem_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:31:50.53199+00:00
-- url     : https://prove2.me/theorems/22b889d8-4b3e-4d2e-8f70-8e554d3dd137
-- title:
--   4.17, p. 459 — for a Hungarian tree J, M₁ is maximum in G − J iff M₁ with any maximum matching of J is maximum in G
-- statement:
--   Let $J$ be a Hungarian tree in a finite graph $G$ (an alternating tree whose outer vertices are joined by edges of $G$ only to its inner vertices), and let $G - J$ be the subgraph induced on the vertices not in $J$. For a matching $M_1$ of $G - J$,
--
--   $$M_1 \text{ is maximum in } G - J \iff M_1 \cup M_J \text{ is a maximum matching of } G \text{ for every maximum matching } M_J \text{ of } J.$$
--
--   A Hungarian tree can therefore be removed from the graph once found: the part of the graph it spans can be matched independently of the rest.
--
--   **Formalization Note** "Together with any maximum matching $M_J$ of $J$" is read as "every"; all maximum matchings of $J$ have the same cardinality, so "some" would be equivalent. Matchings of $J$ and of $G - J$ are matchings of $G$ using only edges of $J$, respectively of $G - J$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 459, 4.17

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Duality

theorem theorem_4_17 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (J : AltTree G) (hJ : IsHungarianTree G J)
    (M₁ : Finset E) (hM₁ : IsMatchingIn G (deleteSub G J.toSub) M₁) :
    IsMaxMatchingIn G (deleteSub G J.toSub) M₁ ↔
      ∀ MJ : Finset E, IsMaxMatchingIn G J.toSub MJ → IsMaxMatching G (M₁ ∪ MJ) := by sorry

end PathsTreesFlowers.Duality
