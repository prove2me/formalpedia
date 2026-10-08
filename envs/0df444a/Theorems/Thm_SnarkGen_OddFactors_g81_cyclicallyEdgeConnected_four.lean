-- Prove2me | Theorems.Thm_SnarkGen_OddFactors_g81_cyclicallyEdgeConnected_four
-- name    : SnarkGen.OddFactors.g81_cyclicallyEdgeConnected_four
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:52.198321+00:00
-- url     : https://prove2.me/theorems/7fa67adb-f5a3-4a2e-8a3e-90c6f7927a2d
-- title:
--   Appendix 8.1 — the graph $G_{8.1}$ is cyclically 4-edge connected
-- statement:
--   Let $G_{8.1}$ be the 26-vertex graph of Appendix 8.1. Then $G_{8.1}$ is cyclically 4-edge connected: for every set $S$ of at most three edges of $G_{8.1}$,
--   $$G_{8.1} - S \ \text{ has at most one connected component that contains a cycle}.$$
--
--   Cyclic 4-edge connectivity is one of the four conditions in the definition of a snark (Section 2). The value 4 cannot be raised for this graph: deleting the four edges $\{7,11\}, \{8,12\}, \{9,13\}, \{10,14\}$ (paper numbering) leaves two components that both contain cycles, so $G_{8.1}$ is not cyclically 5-edge connected.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2 (cyclically k-edge connected, snark); p. 11, Observation 4.12; p. 29, Appendix 8.1

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_Snark
import Definitions.Def_SnarkGen_OddFactors_G81

namespace SnarkGen.OddFactors

/-- The graph `G₈.₁` of Appendix 8.1 (arXiv:1206.6690v3, p. 29) is cyclically 4-edge connected
(p. 4): deleting at most three of its edges never leaves two distinct components that both contain
a cycle. -/
theorem g81_cyclicallyEdgeConnected_four : SnarkGen.Zhang.CyclicallyEdgeConnected G81 4 := by sorry

end SnarkGen.OddFactors
