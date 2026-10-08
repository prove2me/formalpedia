-- Prove2me | Theorems.Thm_SnarkGen_EdgeInsertion_lemma_3_1
-- name    : SnarkGen.EdgeInsertion.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:19.63228+00:00
-- url     : https://prove2.me/theorems/2b4392ca-27d2-46a1-8255-96ec6bf69b20
-- title:
--   Lemma 3.1 — a cubic graph is 3-edge-colourable iff it has an even 2-factor
-- statement:
--   Let $G$ be a finite cubic graph (every vertex has degree $3$). Then
--   $$\chi'(G) \le 3 \iff G \text{ has a 2-factor all of whose cycles have even length.}$$
--   In the paper's words, a cubic graph is colourable if and only if it has oddness $0$.
--
--   This classical equivalence turns 3-edge-colourability into a statement about 2-factors; it is the bridge used in §3.1 to show that the edge insertion operation preserves colourability.
--
--   **Formalization Note** Colourability is `G.lineGraph.Colorable 3` and an even 2-factor is a spanning 2-regular subgraph `F ≤ G` whose connected components all have an even number of vertices. The paper's "oddness 0" is rendered by its second sentence (existence of an even 2-factor), since the paper defines oddness only for bridgeless graphs.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 5, Lemma 3.1

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_EdgeInsertion_EvenTwoFactor

namespace SnarkGen.EdgeInsertion

/-- Lemma 3.1 (arXiv:1206.6690v3, p. 5): a cubic graph is colourable (has a proper
3-edge-colouring) if and only if it has a 2-factor all of whose cycles have even length. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) :
    Colourable G ↔ ∃ F : SimpleGraph V, IsEvenTwoFactor G F := by sorry

end SnarkGen.EdgeInsertion
