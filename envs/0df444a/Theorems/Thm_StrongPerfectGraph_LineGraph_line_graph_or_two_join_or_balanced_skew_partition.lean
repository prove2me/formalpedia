-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_line_graph_or_two_join_or_balanced_skew_partition
-- name    : StrongPerfectGraph.LineGraph.line_graph_or_two_join_or_balanced_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:48:42.571978+00:00
-- url     : https://prove2.me/theorems/46dcf4c8-4308-4ec0-81d4-86c759c9dd94
-- title:
--   5.1, p. 72 — a Berge graph containing a nondegenerate L(H), H a bipartite subdivision of K4, is a line graph or decomposes
-- statement:
--   Let $G$ be a Berge graph, and assume that some nondegenerate $L(H)$ is an induced subgraph of $G$, where $H$ is a bipartite subdivision of $K_4$. Then
--
--   $$G \text{ is a line graph}, \quad\text{or}\quad G \text{ admits a proper 2-join}, \quad\text{or}\quad G \text{ admits a balanced skew partition}.$$
--
--   This is step 1.8.1 of the proof of the strong perfect graph theorem: a Berge graph that contains a substantial line graph is itself a line graph unless it decomposes. The paper's trailing sentence "In particular, 1.8.1 holds" is a corollary and is not stated here.
--
--   **Formalization Note** "Line graph" means the line graph of some finite simple graph, not necessarily bipartite. "$L(H)$ is an induced subgraph of $G$" is an induced graph embedding of Mathlib's line graph of $H$ into $G$, and nondegeneracy means no $4$-cycle of $H$ passes through its four degree-three vertices.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 72, 5.1

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision
import Definitions.Def_StrongPerfectGraph_LineGraph_IsDegenerate

namespace StrongPerfectGraph.LineGraph

theorem line_graph_or_two_join_or_balanced_skew_partition {V U : Type*} [Fintype V] [Fintype U]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (H : SimpleGraph U)
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H) (hbip : H.IsBipartite)
    (hnd : ¬ IsDegenerateK4Subdivision H) (hL : Nonempty (H.lineGraph ↪g G)) :
    StrongPerfectGraph.Main.IsLineGraph G ∨ StrongPerfectGraph.Main.IsProperTwoJoin G ∨ StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.LineGraph
