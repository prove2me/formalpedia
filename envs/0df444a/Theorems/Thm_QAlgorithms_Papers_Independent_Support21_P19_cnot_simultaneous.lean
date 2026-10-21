-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_cnot_simultaneous
-- name    : QAlgorithms.Papers.Independent.Support21.P19.cnot_simultaneous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:01:02.330067+00:00
-- url     : https://prove2.me/theorems/862569b8-8327-4ede-a457-e96093f9c52a
-- title:
--   Eq. (3): entanglement-assisted simultaneous coherent communication
-- statement:
--   One Alice-controlled CNOT and one supplied normalized EPR pair implement a coherent bit in each direction simultaneously:
--
--   $$
--   \mathrm{CNOT}+[qq]\ge[q\to qq]+[qq\leftarrow q].
--   $$
--
--   The simulation is exact as a bipartite channel, including joint superpositions of both messages and arbitrary external references. The sole shared entangled input is the one charged EPR pair; there is no uncounted catalyst or classical feedback. This resource claim is independent of the unresolved literal encoding formula printed as Eq. (2).
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 2, Eq. (3): entanglement-assisted simultaneous coherent communication

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Eq. (3): simultaneous opposite-direction cobits from one CNOT and one EPR pair.
The unresolved Y in Eq. (2) is not a hypothesis or an identity asserted here. -/
theorem cnot_simultaneous :
    Exact cnotResource (budget 1 1 0 0 0 0 0 0) (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
