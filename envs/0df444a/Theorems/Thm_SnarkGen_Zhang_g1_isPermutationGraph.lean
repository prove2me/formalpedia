-- Prove2me | Theorems.Thm_SnarkGen_Zhang_g1_isPermutationGraph
-- name    : SnarkGen.Zhang.g1_isPermutationGraph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:24.322804+00:00
-- url     : https://prove2.me/theorems/e2031a84-b2a2-4b36-9f43-8270341fe7ed
-- title:
--   Appendix 8.6 — the graph $G_1$ is a permutation graph
-- statement:
--   Let $G_1$ be the first graph of Appendix 8.6 (34 vertices, paper vertex $i$ renamed $i-1$). Then $G_1$ is a **permutation graph**: it is cubic, and its vertex set splits into two sets $A$ and $V \setminus A$ such that the induced subgraphs
--   $$
--   G_1[A] \quad\text{and}\quad G_1[V\setminus A]
--   $$
--   are both cycles (connected and $2$-regular). Equivalently, $G_1$ has a $2$-factor consisting of two induced cycles; since $G_1$ has $34$ vertices, both are $17$-cycles.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6 (heading and first list); p. 8, Section 4.2 (definition of permutation graph)

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1
import Definitions.Def_SnarkGen_Zhang_IsPermutationGraph

namespace SnarkGen.Zhang

theorem g1_isPermutationGraph : IsPermutationGraph g1 := by sorry

end SnarkGen.Zhang
