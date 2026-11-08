-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_basic_perfect
-- name    : StrongPerfectGraph.Main.basic_perfect
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T06:14:39.89808+00:00
-- url     : https://prove2.me/theorems/81b8bf2f-75fe-44b6-9872-ad8f794552bd
-- title:
--   All basic graphs are perfect
-- statement:
--   Let $G$ be a finite simple graph. Following the paper, $G$ is *basic* if one of the following holds:
--
--   1. $G$ is bipartite;
--   2. $\overline G$ is bipartite;
--   3. $G$ is isomorphic to the line graph $L(H)$ of a bipartite graph $H$;
--   4. $\overline G$ is isomorphic to the line graph of a bipartite graph;
--   5. $G$ is a double split graph.
--
--   Then every basic graph is perfect:
--
--   $$G\ \text{basic}\ \Longrightarrow\ \chi(G|X)=\omega(G|X)\ \text{ for all } X\subseteq V(G).$$
--
--   The paper states "It is easy to see that all basic graphs are perfect": for bipartite graphs this is trivial; for line graphs of bipartite graphs it is König's edge-colouring theorem; for their complements it follows from Lovász's theorem 1.1; and for double split graphs it is left to the reader. It is one of the ingredients of the derivation of Theorem 1.2 from the decomposition theorem 1.3.
--
--   **Formalization Note** `IsBasic` is the mission definition; line graphs are taken of a graph on `Fin n`, up to graph isomorphism.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), 51-229, p. 53 (sentence "It is easy to see that all basic graphs are perfect", after the definition of basic graphs)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- Every basic graph is perfect (p. 53). -/
theorem basic_perfect {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBasic G) : IsPerfect G := by sorry

end StrongPerfectGraph.Main
