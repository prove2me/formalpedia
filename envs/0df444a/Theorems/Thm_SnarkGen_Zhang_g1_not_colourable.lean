-- Prove2me | Theorems.Thm_SnarkGen_Zhang_g1_not_colourable
-- name    : SnarkGen.Zhang.g1_not_colourable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:39.312104+00:00
-- url     : https://prove2.me/theorems/5ff3ee9b-6340-4674-8eb2-7a20adbe940c
-- title:
--   Appendix 8.6 — the graph $G_1$ is uncolourable
-- statement:
--   Let $G_1$ be the first graph of Appendix 8.6 (34 vertices, 51 edges, paper vertex $i$ renamed $i-1$). Then $G_1$ is **uncolourable**: there is no map
--   $$
--   c : E(G_1) \to \{1,2,3\}
--   $$
--   giving distinct colours to any two distinct edges that share an endpoint. In other words, the chromatic index of $G_1$ is $4$.
--
--   Uncolourability is the defining property of a snark and the hardest to certify by hand.
--
--   **Formalization Note** "Colourable" is `G.lineGraph.Colorable 3`, a proper $3$-colouring of the line graph.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6 (heading and first list); p. 4, Section 2 (definition of snark)

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable

namespace SnarkGen.Zhang

theorem g1_not_colourable : ¬ SnarkGen.EdgeInsertion.Colourable g1 := by sorry

end SnarkGen.Zhang
