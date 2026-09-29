-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_large_subgraphs_or_small_cut
-- name    : RobertsonSeymour1986.GM5.large_subgraphs_or_small_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:02:47.364842+00:00
-- url     : https://prove2.me/theorems/f4271dfb-7770-4212-84ff-965afb996a77
-- title:
--   (6.3) $k$ disjoint large connected subgraphs, or fewer than $k$ vertices leaving only small components
-- statement:
--   Let $G$ be a finite connected graph and let $k>0$ be an integer. Then at least one of the following holds:
--
--   1. there are $k$ disjoint connected subgraphs of $G$, each with at least
--   $$2(3^k-1)^{-1}|V(G)|$$
--   vertices;
--   2. there is $X\subseteq V(G)$ with $|X|<k$ such that every component of $G\setminus X$ has fewer than $|V(G)|/3$ vertices.
--
--   The general version (6.4) for possibly disconnected graphs follows from this one.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (6.3), p. 104 (PDF p. 13); DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- (6.3): a connected graph has either `k` disjoint large connected subgraphs, or fewer than `k`
vertices whose deletion leaves only components with fewer than `|V(G)|/3` vertices.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (6.3), p. 104 (PDF p. 13): "Let G be a connected graph, and let k > 0 be an integer. Then at
least one of the following is true: (i) there are k disjoint connected subgraphs of G, each with at
least 2(3^k − 1)^{−1}|V(G)| vertices; (ii) there exists X ⊆ V(G) with |X| < k such that every
component of G\X has fewer than |V(G)|/3 vertices."

**Formalization Note** No `θ`. The bounds `2(3^k − 1)^{−1}|V(G)|` and `|V(G)|/3` are compared in
`ℚ` (`3^k − 1 > 0` since `k > 0`). A component of `G\X` is a connected component of
`G.induce Xᶜ`; its number of vertices is `C.supp.ncard`. -/
theorem large_subgraphs_or_small_cut {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (k : ℕ) (hk : 0 < k) :
    (∃ B : Fin k → G.Subgraph, (∀ i, (B i).Connected) ∧
        Pairwise (fun i i' => Disjoint (B i).verts (B i').verts) ∧
        ∀ i, 2 * ((3 : ℚ) ^ k - 1)⁻¹ * (Fintype.card V : ℚ) ≤ ((B i).verts.ncard : ℚ)) ∨
    (∃ X : Finset V, X.card < k ∧
        ∀ C : (G.induce ((X : Set V)ᶜ)).ConnectedComponent,
          (C.supp.ncard : ℚ) < (Fintype.card V : ℚ) / 3) := by sorry

end RobertsonSeymour1986.GM5
