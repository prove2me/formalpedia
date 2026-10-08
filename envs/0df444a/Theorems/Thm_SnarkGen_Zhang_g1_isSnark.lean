-- Prove2me | Theorems.Thm_SnarkGen_Zhang_g1_isSnark
-- name    : SnarkGen.Zhang.g1_isSnark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:35.892612+00:00
-- url     : https://prove2.me/theorems/9fa86fe3-2109-4fa9-8483-bd6e15fb7408
-- title:
--   Appendix 8.6 — the graph $G_1$ is a snark
-- statement:
--   Let $G_1$ be the first graph of Appendix 8.6 (34 vertices, paper vertex $i$ renamed $i-1$). Then $G_1$ is a **snark**:
--   $$
--   G_1 \text{ is cubic},\quad G_1 \text{ is uncolourable},\quad G_1 \text{ is cyclically 4-edge connected},\quad g(G_1) \ge 5.
--   $$
--
--   It combines the cubicity, girth and uncolourability of $G_1$ with its cyclic $5$-edge connectivity, which implies cyclic $4$-edge connectivity.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6 (heading and first list); p. 4, Section 2 (definition of snark)

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1
import Definitions.Def_SnarkGen_Zhang_IsSnark

namespace SnarkGen.Zhang

theorem g1_isSnark : IsSnark g1 := by sorry

end SnarkGen.Zhang
