-- Prove2me | Theorems.Thm_SnarkGen_Zhang_g1_isRegularOfDegree_three
-- name    : SnarkGen.Zhang.g1_isRegularOfDegree_three
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:29.662967+00:00
-- url     : https://prove2.me/theorems/7a3465a2-4242-47d1-8947-f6a620495a06
-- title:
--   Appendix 8.6 — the graph $G_1$ is cubic
-- statement:
--   Let $G_1$ be the first graph of Appendix 8.6 (34 vertices, 51 edges, decoded from the printed list of higher-numbered neighbours, with the paper's vertex $i$ renamed $i-1$). Then $G_1$ is **cubic**: every vertex has exactly three neighbours,
--   $$
--   \deg_{G_1}(v) = 3 \quad \text{for all } v \in \{0,\dots,33\}.
--   $$
--
--   This is the first of the properties that make $G_1$ a snark, and it also certifies that the decoding of the printed list is consistent.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6 (heading and first list); p. 4, Section 2 (definition of snark)

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1

namespace SnarkGen.Zhang

theorem g1_isRegularOfDegree_three : g1.IsRegularOfDegree 3 := by sorry

end SnarkGen.Zhang
