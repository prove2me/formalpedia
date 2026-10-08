-- Prove2me | Theorems.Thm_SnarkGen_EdgeInsertion_theorem_3_3
-- name    : SnarkGen.EdgeInsertion.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:14.296439+00:00
-- url     : https://prove2.me/theorems/fe6ec70a-faed-4548-923a-bb6b6e33c9a3
-- title:
--   Theorem 3.3 — inserting an edge between two edges of one bicoloured cycle of a 3-coloured cubic graph gives a colourable graph
-- statement:
--   Let $G = (V,E)$ be a finite cubic graph with a 3-colouring (proper edge colouring) $C : E \to \{0,1,2\}$, and let $i \ne j$ be two colours. Write $G_{ij}$ for the 2-factor of $G$ formed by the edges coloured $i$ or $j$. Let $e = ab$ and $e' = cd$ be two distinct edges of $G$, each coloured $i$ or $j$, which belong to the same cycle of $G_{ij}$. Let $G'$ be the graph obtained from $G$ by the edge insertion operation applied to $e$ and $e'$ (subdivide $e$ by a new vertex $x$, subdivide $e'$ by a new vertex $y$, and add the edge $xy$). Then
--   $$\chi'(G') \le 3,$$
--   that is, $G'$ is colourable.
--
--   The edges may share an end-vertex. In the generation algorithm of §3.1, a 3-colouring of a graph on $n-2$ vertices thus rules out, in one stroke, every edge pair lying on a common bicoloured cycle as a candidate for producing a snark on $n$ vertices.
--
--   **Formalization Note** The colouring is `C : G.lineGraph.Coloring (Fin 3)`. "$e$ and $e'$ belong to the same cycle of $G_{ij}$" is encoded as: $ab$ and $cd$ are edges of $G_{ij}$ (so they are edges of $G$ coloured $i$ or $j$) and $c$ is reachable from $a$ in $G_{ij}$. Distinctness is `s(a, b) ≠ s(c, d)`. The new vertices are `Sum.inr 0` and `Sum.inr 1` of `V ⊕ Fin 2`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 5, Theorem 3.3

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_EdgeInsertion_twoColourFactor
import Definitions.Def_SnarkGen_EdgeInsertion_insertEdge

namespace SnarkGen.EdgeInsertion

/-- Theorem 3.3 (arXiv:1206.6690v3, p. 5): let `G` be a cubic graph with a 3-edge-colouring `C`,
and let `i ≠ j` be two colours. If two distinct edges `e = ab` and `e' = cd` of `G`, each coloured
`i` or `j`, belong to the same cycle of the 2-factor formed by the edges coloured `i` or `j`, then
the graph obtained from `G` by the edge insertion operation applied to `e` and `e'` is
colourable. -/
theorem theorem_3_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (C : G.lineGraph.Coloring (Fin 3))
    (i j : Fin 3) (hij : i ≠ j) (a b c d : V)
    (hab : (twoColourFactor C i j).Adj a b) (hcd : (twoColourFactor C i j).Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hsame : (twoColourFactor C i j).Reachable a c) :
    Colourable (insertEdge G s(a, b) s(c, d)) := by sorry

end SnarkGen.EdgeInsertion
