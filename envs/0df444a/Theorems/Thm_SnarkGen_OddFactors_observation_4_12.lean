-- Prove2me | Theorems.Thm_SnarkGen_OddFactors_observation_4_12
-- name    : SnarkGen.OddFactors.observation_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:46.072197+00:00
-- url     : https://prove2.me/theorems/1dd180ce-6880-43ee-ae76-13e9d490a155
-- title:
--   Observation 4.12 — a snark on 26 vertices all of whose 2-factors consist of odd cycles (Conjecture 4.11 is false)
-- statement:
--   Abreu, Labbate and Sheehan conjectured (Conjecture 4.11 of the paper) that the only snarks where all 2-factors consist of only odd cycles are the Petersen graph, the Blanuša-2 snark and the Flower snarks. The paper shows that this conjecture is false, with the counterexample $G_{8.1}$ of Appendix 8.1.
--
--   Let $G_{8.1}$ be the 26-vertex graph of Appendix 8.1. Then
--
--   1. $G_{8.1}$ is a snark: it is cubic, uncolourable, cyclically 4-edge connected and has girth at least 5; and
--   2. every 2-factor of $G_{8.1}$ consists of only odd cycles.
--
--   $$G_{8.1} \text{ is a snark} \quad\text{and}\quad \forall F \text{ 2-factor of } G_{8.1},\ \text{every cycle of } F \text{ has odd length}.$$
--
--   Since $G_{8.1}$ has 26 vertices, it is none of the graphs the conjecture lists: the Petersen graph has 10 vertices, the Blanuša-2 snark has 18, and the Flower snark $J_k$ has $4k$ vertices, while 26 is not divisible by 4. Hence the statement refutes Conjecture 4.11. The graph $G_{8.1}$ does have 2-factors (56 of them), so the second clause is not vacuous.
--
--   Observation 4.12 further says that this is the smallest counterexample and that there is exactly one more on 34 vertices. Those claims rest on an exhaustive computer enumeration and are not part of this statement.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 11, Refuted Conjecture 4.11 and Observation 4.12 (existence half); p. 29, Appendix 8.1

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_Snark
import Definitions.Def_SnarkGen_OddFactors_TwoFactor
import Definitions.Def_SnarkGen_OddFactors_G81

namespace SnarkGen.OddFactors

/-- **Observation 4.12** (arXiv:1206.6690v3, p. 11), existence half: the graph `G₈.₁` on 26
vertices of Appendix 8.1 (p. 29) is a snark (cubic, uncolourable, cyclically 4-edge connected, girth
at least 5) all of whose 2-factors consist of only odd cycles. Since 26 is neither 10, nor 18, nor
divisible by 4, it is not the Petersen graph, the Blanuša-2 snark or a Flower snark, so it refutes
Conjecture 4.11 (Abreu, Labbate, Sheehan). -/
theorem observation_4_12 : IsSnark G81 ∧ AllTwoFactorsOdd G81 := by sorry

end SnarkGen.OddFactors
