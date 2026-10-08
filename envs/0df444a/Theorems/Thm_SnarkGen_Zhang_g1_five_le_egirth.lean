-- Prove2me | Theorems.Thm_SnarkGen_Zhang_g1_five_le_egirth
-- name    : SnarkGen.Zhang.g1_five_le_egirth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:33.327306+00:00
-- url     : https://prove2.me/theorems/7e2a95e8-7a00-41db-a53d-6d1c56c7e3f7
-- title:
--   Appendix 8.6 — the graph $G_1$ has girth at least 5
-- statement:
--   Let $G_1$ be the first graph of Appendix 8.6 (34 vertices, paper vertex $i$ renamed $i-1$). The **girth** of a graph is the number of vertices in a shortest cycle. Then $G_1$ has no cycle of length $3$ or $4$:
--   $$
--   g(G_1) \ge 5.
--   $$
--
--   Girth at least $5$ is one of the defining conditions of a snark.
--
--   **Formalization Note** The girth is Mathlib's extended girth `egirth`, which is $\infty$ for an acyclic graph; the statement `5 ≤ g1.egirth` says every cycle has length at least $5$.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6 (heading and first list); p. 4, Section 2 (definition of girth and of snark)

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1

namespace SnarkGen.Zhang

theorem g1_five_le_egirth : 5 ≤ g1.egirth := by sorry

end SnarkGen.Zhang
