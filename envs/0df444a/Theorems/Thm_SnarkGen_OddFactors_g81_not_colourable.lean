-- Prove2me | Theorems.Thm_SnarkGen_OddFactors_g81_not_colourable
-- name    : SnarkGen.OddFactors.g81_not_colourable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:01.029197+00:00
-- url     : https://prove2.me/theorems/da05a57d-de44-4f94-872a-e9b3a4664f92
-- title:
--   Appendix 8.1 — the graph $G_{8.1}$ is uncolourable
-- statement:
--   Let $G_{8.1}$ be the 26-vertex graph of Appendix 8.1. Then $G_{8.1}$ is uncolourable: its edges admit no proper 3-colouring,
--   $$\chi'(G_{8.1}) > 3.$$
--
--   Uncolourability is the defining property of a snark (Section 2), and $G_{8.1}$ must have it to be a counterexample to Conjecture 4.11.
--
--   **Formalization Note** "Colourable" means that the line graph of $G_{8.1}$ is vertex 3-colourable.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2 (snark); p. 11, Observation 4.12; p. 29, Appendix 8.1

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_Snark
import Definitions.Def_SnarkGen_OddFactors_G81

namespace SnarkGen.OddFactors

/-- The graph `G₈.₁` of Appendix 8.1 (arXiv:1206.6690v3, p. 29) is uncolourable: its edges admit no
proper 3-colouring. -/
theorem g81_not_colourable : ¬ SnarkGen.EdgeInsertion.Colourable G81 := by sorry

end SnarkGen.OddFactors
