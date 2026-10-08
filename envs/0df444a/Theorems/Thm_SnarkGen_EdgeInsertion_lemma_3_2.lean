-- Prove2me | Theorems.Thm_SnarkGen_EdgeInsertion_lemma_3_2
-- name    : SnarkGen.EdgeInsertion.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:07.773979+00:00
-- url     : https://prove2.me/theorems/94ccc779-b9bf-4c81-baa0-a6959794ce95
-- title:
--   Lemma 3.2 — inserting an edge between two edges of one cycle of an even 2-factor gives a colourable graph
-- statement:
--   Let $G = (V,E)$ be a finite cubic graph and let $F$ be an even 2-factor of $G$. Let $e = ab$ and $e' = cd$ be two distinct edges of $F$ that lie on the same cycle of $F$. Let $G'$ be the graph obtained from $G$ by the edge insertion operation applied to $e$ and $e'$ (subdivide $e$ by a new vertex $x$, subdivide $e'$ by a new vertex $y$, and add the edge $xy$). Then
--   $$\chi'(G') \le 3,$$
--   that is, $G'$ is colourable.
--
--   The edges $e$ and $e'$ may share an end-vertex. Lemma 3.2 is the look-ahead criterion of the snark generation algorithm: such edge pairs never lead to a snark and need not be tried.
--
--   **Formalization Note** "$e$ and $e'$ lie on the same cycle of $F$" is encoded as: $ab$ and $cd$ are edges of $F$ and $c$ is reachable from $a$ in $F$ (the cycles of a 2-factor are its connected components). Distinctness is `s(a, b) ≠ s(c, d)`. The new vertices are `Sum.inr 0` and `Sum.inr 1` of `V ⊕ Fin 2`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 5, Lemma 3.2

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_EdgeInsertion_EvenTwoFactor
import Definitions.Def_SnarkGen_EdgeInsertion_insertEdge

namespace SnarkGen.EdgeInsertion

/-- Lemma 3.2 (arXiv:1206.6690v3, p. 5): let `F` be an even 2-factor of a cubic graph `G`, and
let `e = ab` and `e' = cd` be two distinct edges of `F` lying on the same cycle of `F` (the same
connected component of `F`). Then the graph obtained from `G` by the edge insertion operation
applied to `e` and `e'` is colourable. -/
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (F : SimpleGraph V)
    (hF : IsEvenTwoFactor G F) (a b c d : V) (hab : F.Adj a b) (hcd : F.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hsame : F.Reachable a c) :
    Colourable (insertEdge G s(a, b) s(c, d)) := by sorry

end SnarkGen.EdgeInsertion
