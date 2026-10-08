-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_14
-- name    : PathsTreesFlowers.Duality.lemma_4_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:11.727989+00:00
-- url     : https://prove2.me/theorems/0ada799a-0c63-43ad-ab80-7138d746c0a0
-- title:
--   4.14, p. 458 — every matching M₁ of G/B extends by a maximum matching M_B of the odd circuit B to a matching of G
-- statement:
--   Let $B$ be an odd circuit in a finite graph $G$, with vertex set $U$, and let $G/B$ be the graph obtained by shrinking $U$ to a single vertex. For every matching $M_1$ of $G/B$ there exists a maximum matching $M_B$ of $B$ such that
--
--   $$M = M_1 \cup M_B$$
--
--   is a matching of $G$, where the edges of $M_1$ are regarded as edges of $G$.
--
--   This is the "only if" direction of 4.12 in a stronger form: it holds for any odd circuit, without reference to a matching of $G$, and it is how an augmentation in a shrunken graph is carried back to $G$.
--
--   **Formalization Note** A maximum matching of $B$ is one of largest cardinality among matchings using edges of the circuit only (it has $k$ edges when $B$ has $2k+1$ vertices). Shrinking $B$ removes every edge with both end-points in $U$, including chords of $B$ (4.9).
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 458, 4.14

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Duality

theorem lemma_4_14 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (vs : List V) (es : List E) (hB : IsCircuit G vs es) (hodd : Odd vs.length)
    (M₁ : Finset {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e})
    (hM₁ : EdmondsMatching65.Polyhedron.IsMatching (shrink G (blockPartition vs.toFinset)) M₁) :
    ∃ MB : Finset E, IsMaxMatchingOn G es.toFinset MB ∧
      EdmondsMatching65.Polyhedron.IsMatching G
        (M₁.map (Function.Embedding.subtype _) ∪ MB) := by sorry

end PathsTreesFlowers.Duality
