-- Prove2me | Theorems.Thm_SnarkGen_EdgeInsertion_twoColourFactor_isEvenTwoFactor
-- name    : SnarkGen.EdgeInsertion.twoColourFactor_isEvenTwoFactor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:17.383977+00:00
-- url     : https://prove2.me/theorems/0ff853b3-d41d-433d-9b0d-d33d6b827e73
-- title:
--   §3.1, p. 5 — in a 3-colouring of a cubic graph, two colour classes form an even 2-factor
-- statement:
--   Let $G = (V,E)$ be a finite cubic graph, let $C : E \to \{0,1,2\}$ be a proper 3-edge-colouring of $G$, and let $i \ne j$ be two colours. Then the spanning subgraph
--   $$G_{ij} = \bigl(V,\ \{e \in E : C(e) \in \{i,j\}\}\bigr)$$
--   is a 2-factor of $G$ all of whose cycles have even length.
--
--   This is the observation by which Lemma 3.2 is applied to a 3-colouring: each 3-colouring of a cubic graph yields three even 2-factors, one for each pair of colours.
--
--   **Formalization Note** The colouring is `C : G.lineGraph.Coloring (Fin 3)`; the 2-factor and evenness conventions are those of the definition `EvenTwoFactor` (spanning 2-regular subgraph, every component with an even number of vertices).
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 5, §3.1 (unnumbered sentence between Lemma 3.2 and Theorem 3.3)

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_EvenTwoFactor
import Definitions.Def_SnarkGen_EdgeInsertion_twoColourFactor

namespace SnarkGen.EdgeInsertion

/-- arXiv:1206.6690v3, §3.1, p. 5: in a cubic graph with a 3-edge-colouring `C`, for any two
colours `i ≠ j` the edges coloured `i` or `j` form a 2-factor with all cycles of even length. -/
theorem twoColourFactor_isEvenTwoFactor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    (C : G.lineGraph.Coloring (Fin 3)) (i j : Fin 3) (hij : i ≠ j) :
    IsEvenTwoFactor G (twoColourFactor C i j) := by sorry

end SnarkGen.EdgeInsertion
