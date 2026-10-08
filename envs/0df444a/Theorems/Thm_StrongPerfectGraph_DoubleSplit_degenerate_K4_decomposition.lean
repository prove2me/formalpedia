-- Prove2me | Theorems.Thm_StrongPerfectGraph_DoubleSplit_degenerate_K4_decomposition
-- name    : StrongPerfectGraph.DoubleSplit.degenerate_K4_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:06:01.399085+00:00
-- url     : https://prove2.me/theorems/48a597a9-37e1-4c9a-ab65-f16c93a5c3d7
-- title:
--   9.6, p. 116 — a Berge graph whose appearances of $K_4$ are all degenerate is double split, decomposes, or has no appearance of $K_4$
-- statement:
--   Let $G$ be a Berge graph such that every appearance of $K_4$ in $G$ and in $\overline{G}$ is degenerate, and no induced subgraph of $G$ is isomorphic to $L(K_{3,3})$. Then at least one of the following holds:
--
--   1. $G$ is a double split graph;
--   2. $G$ admits a balanced skew partition;
--   3. one of $G, \overline{G}$ admits a proper 2-join;
--   4. there is no appearance of $K_4$ in either $G$ or $\overline{G}$.
--
--   This is step 1.8.3 of the proof of the strong perfect graph theorem: together with 5.1 and 5.2 it disposes of all Berge graphs containing the line graph of a bipartite subdivision of $K_4$.
--
--   **Formalization Note** "Every appearance of $K_4$ in $G$ is degenerate" is stated as the absence of a nondegenerate appearance; "no induced subgraph isomorphic to $L(K_{3,3})$" as the absence of an induced embedding of $L(K_{3,3})$ into $G$ (it concerns $G$ only, not $\overline{G}$).
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 116, 9.6 (= 1.8.3, p. 60)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears

namespace StrongPerfectGraph.DoubleSplit

/-- 9.6 (p. 116), step 1.8.3 of the proof of the strong perfect graph theorem. Let `G` be Berge,
such that every appearance of `K₄` in `G` and in `G̅` is degenerate, and no induced subgraph of `G`
is isomorphic to `L(K₃,₃)`. Then `G` is a double split graph, or `G` admits a balanced skew
partition, or one of `G, G̅` admits a proper 2-join, or there is no appearance of `K₄` in either
`G` or `G̅`. -/
theorem degenerate_K4_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G)
    (hdeg : ¬ StrongPerfectGraph.LineGraph.HasNondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.HasNondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (hK33 : IsEmpty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ↪g G)) :
    StrongPerfectGraph.Main.IsDoubleSplit G ∨ StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G ∨
      StrongPerfectGraph.Main.IsProperTwoJoin G ∨ StrongPerfectGraph.Main.IsProperTwoJoin Gᶜ ∨
      (¬ StrongPerfectGraph.LineGraph.Appears (⊤ : SimpleGraph (Fin 4)) G ∧ ¬ StrongPerfectGraph.LineGraph.Appears (⊤ : SimpleGraph (Fin 4)) Gᶜ) := by sorry

end StrongPerfectGraph.DoubleSplit
