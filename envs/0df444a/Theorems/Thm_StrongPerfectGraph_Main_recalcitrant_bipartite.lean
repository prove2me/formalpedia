-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_recalcitrant_bipartite
-- name    : StrongPerfectGraph.Main.recalcitrant_bipartite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:14:52.75712+00:00
-- url     : https://prove2.me/theorems/2bba9a85-6ebc-429c-bcbe-9acfe2a7e262
-- title:
--   13.5 — recalcitrant graphs are bipartite up to complement
-- statement:
--   Let $G$ be a recalcitrant graph, meaning a Berge graph with the listed line-graph, double-split, 2-join, homogeneous-pair, and balanced-skew-partition outcomes excluded. Then $G$ or its complement is bipartite:
--
--   $$\operatorname{Recalcitrant}(G)\quad\Longrightarrow\quad G\text{ bipartite}\ \lor\ \overline G\text{ bipartite}.$$
--
--   The paper identifies this as the capstone of its long structural argument; it implies the decomposition theorem 1.3.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 154, 13.5

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsRecalcitrant

namespace StrongPerfectGraph.Main

/-- The paper's recalcitrant-graph capstone, Theorem 13.5. -/
theorem recalcitrant_bipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsRecalcitrant G) :
    G.IsBipartite ∨ Gᶜ.IsBipartite := by sorry

end StrongPerfectGraph.Main
