-- Prove2me | Theorems.Thm_VanderbeiLP_Networks_spanning_tree_iff_basis
-- name    : VanderbeiLP.Networks.spanning_tree_iff_basis
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T18:52:53.735984+00:00
-- url     : https://prove2.me/theorems/fa56a43a-5c7a-4cda-824a-0220549ddd09
-- title:
--   Theorem 14.1 — bases of Ã are spanning trees
-- statement:
--   Let $(N,A)$ be a connected network with $m$ nodes, let $r$ be a root node and let $\tilde A$ be the node–arc incidence matrix with the row of $r$ deleted. For every set $T\subseteq A$ of arcs,
--   $$\text{the columns of }\tilde A\text{ indexed by }T\text{ form a basis}\iff T\text{ is a spanning tree}.$$
--   Here a basis is an invertible square submatrix, i.e. $|T|=m-1$ linearly independent columns, and a spanning tree is an arc set that is connected on all of $N$ and acyclic when directions are ignored.
--
--   The theorem translates the algebra of the simplex method on (14.1) into the combinatorics of the network: bases are spanning trees, and pivots exchange one tree arc for another.
--
--   **Formalization Note** The chapter's standing assumption "The network is connected" (p. 202) is a hypothesis. The book proves the direction "spanning tree $\Rightarrow$ basis" and leaves the converse as Exercise 14.12; both are stated.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 205 (PDF 216), Theorem 14.1; standing assumption p. 202

import Mathlib
import Definitions.Def_VanderbeiLP_Networks_Network

namespace VanderbeiLP.Networks

/-- **Theorem 14.1** (Vanderbei, *Linear Programming*, 4th ed., p. 205). For a connected network
`(N, A)` with root node `r`, a square submatrix of the truncated incidence matrix `Ã` is a basis
if and only if the arcs to which its columns correspond form a spanning tree. -/
theorem spanning_tree_iff_basis {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (hconn : IsConnectedNetwork A)
    (r : N) (T : Finset (N × N)) (hT : T ⊆ A) :
    IsBasisArcs r T ↔ IsSpanningTree A T := by sorry

end VanderbeiLP.Networks
