-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_line_graph_bipartite_perfect
-- name    : StrongPerfectGraph.Main.line_graph_bipartite_perfect
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T06:17:16.209352+00:00
-- url     : https://prove2.me/theorems/64e59565-b629-4657-89de-1114cc37bb24
-- title:
--   Line graphs of bipartite graphs are perfect (König)
-- statement:
--   Let $H$ be a finite bipartite graph and let $L(H)$ be its line graph: the vertices of $L(H)$ are the edges of $H$, two of them adjacent when they share an end. If a finite graph $G$ is isomorphic to $L(H)$, then $G$ is perfect:
--
--   $$\chi(G|X)=\omega(G|X)\qquad\text{for every } X\subseteq V(G).$$
--
--   This is König's theorem as cited on p. 53 of the paper: an induced subgraph of $L(H)$ is the line graph of a subgraph of $H$, which is again bipartite, and for a bipartite graph the edge-chromatic number equals the maximum degree, which is the clique number of the line graph. It is the line-graph case of "all basic graphs are perfect".
--
--   **Formalization Note** $H$ is a graph on `Fin n`, and $G$ is given together with an isomorphism `G ≃g H.lineGraph`, matching the line-graph clauses of the mission definition `IsBasic`.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), 51-229, p. 53 ("for line graphs of bipartite graphs it is a theorem of König [15]"), citing D. König, Math. Ann. 77 (1916), 453-465

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- König: the line graph of a bipartite graph is perfect (p. 53, citing [15]). -/
theorem line_graph_bipartite_perfect {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (hH : H.IsBipartite)
    (e : G ≃g H.lineGraph) : IsPerfect G := by sorry

end StrongPerfectGraph.Main
