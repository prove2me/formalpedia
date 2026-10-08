-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_indep_mul_clique_ge
-- name    : TwinWidthI.MinorFree.indep_mul_clique_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:42.227992+00:00
-- url     : https://prove2.me/theorems/48717d30-5b44-44ec-bdd5-15f3fe17955f
-- title:
--   p. 3:27 — α(H)ω(H) ≥ |V(H)| for intersection graphs of subtrees of a tree
-- statement:
--   Suppose a finite graph $H$ is the intersection graph of subtrees of a tree: each vertex $w$ has a connected subtree $F(w)$, and distinct vertices are adjacent exactly when their subtrees intersect. Then
--
--   $$
--   |V(H)|\le \alpha(H)\,\omega(H),
--   $$
--
--   where $\alpha(H)$ is the largest size of an independent set and $\omega(H)$ the largest size of a clique. The paper applies this to the intersection graph of enhanced DFS subtrees.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:27, proof of Theorem 6.3, paragraph 'The intersection graph H of the enhancements'

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting
import Definitions.Def_TwinWidthI_MinorFree_Setting

namespace TwinWidthI.MinorFree

/-- The numerical consequence of perfection for a finite subtree intersection graph (p. 3:27). -/
theorem indep_mul_clique_ge {W β : Type} [Fintype W]
    (H : SimpleGraph W) (T : SimpleGraph β) (F : W → Set β)
    (hF : GavrilSubtree.Chordal.IsSubtreeRep H T F) :
    Fintype.card W ≤ H.indepNum * H.cliqueNum := by sorry

end TwinWidthI.MinorFree
