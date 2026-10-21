-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_superdense_quantum_states
-- name    : QAlgorithms.Papers.Independent.Support21.P19.superdense_quantum_states
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:08:33.53006+00:00
-- url     : https://prove2.me/theorems/11906a82-a39f-4883-a96b-c6a5e84b4a25
-- title:
--   Corollary 4 (super-dense coding of quantum states)
-- statement:
--   One forward qubit channel together with one consumed EPR pair achieves two remote qubits asymptotically, with the restricted block convention of Eq. (5):
--
--   $$
--   [q\to q]+[qq]\ge2\text{ remote qubits}\qquad(a).
--   $$
--
--   For every $\varepsilon,\delta>0$ and sufficiently large $n$, at most $n$ such paired resource calls prepare any $m$ independently known $m$-qubit pure states satisfying $m^2\ge n(2-\delta)$, with uniform trace-distance error at most $\varepsilon$. Bob's maps are independent of the state descriptions. Exactly one EPR pair per available qubit call is counted as a consumed resource, and no additional externally supplied startup entanglement is allowed. The source attributes the earlier direct proof to Harrow–Hayden–Leung, quant-ph/0307221.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 3, Corollary 4 (super-dense coding of quantum states)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Corollary 4: the one consumed ebit per forward qubit is charged in U itself. -/
theorem superdense_quantum_states :
    RemoteRate (tensorResources (qubitChannel 2) (entangled 2)) 2 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
