-- Prove2me | Theorems.Thm_SnarkGen_Zhang_g1_counterexample
-- name    : SnarkGen.Zhang.g1_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:53.582456+00:00
-- url     : https://prove2.me/theorems/119e2954-bbd5-4c77-b997-98b178a7da54
-- title:
--   Appendix 8.6 — $G_1$ is a cyclically 5-edge-connected permutation snark not isomorphic to the Petersen graph
-- statement:
--   Let $G_1$ be the first graph of Appendix 8.6 (34 vertices, paper vertex $i$ renamed $i-1$) and $P$ the Petersen graph. Then $G_1$ satisfies every hypothesis of Zhang's Conjecture 4.1 and is not the Petersen graph:
--
--   1. $G_1$ is cubic;
--   2. $G_1$ is cyclically $5$-edge connected;
--   3. $G_1$ is a permutation graph;
--   4. $G_1$ is a snark;
--   5. there is no graph isomorphism $G_1 \cong P$.
--
--   This is the content of the Appendix 8.6 heading for its first graph, and the goal (Observation 4.2) follows from it at once.
--
--   **Formalization Note** Item 5 is `IsEmpty (g1 ≃g petersen)`; it holds because the vertex sets have $34$ and $10$ elements.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6 (heading and first list); p. 9, Section 4.2

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1
import Definitions.Def_SnarkGen_Zhang_CyclicallyEdgeConnected
import Definitions.Def_SnarkGen_Zhang_IsSnark
import Definitions.Def_SnarkGen_Zhang_IsPermutationGraph
import Definitions.Def_SnarkGen_Zhang_petersen

namespace SnarkGen.Zhang

theorem g1_counterexample :
    g1.IsRegularOfDegree 3 ∧ CyclicallyEdgeConnected g1 5 ∧ IsPermutationGraph g1 ∧
      IsSnark g1 ∧ IsEmpty (g1 ≃g petersen) := by sorry

end SnarkGen.Zhang
