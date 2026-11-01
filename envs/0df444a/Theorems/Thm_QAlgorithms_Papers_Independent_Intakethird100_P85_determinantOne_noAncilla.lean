-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_determinantOne_noAncilla
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.determinantOne_noAncilla
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:13:25.06989+00:00
-- url     : https://prove2.me/theorems/c0ce9021-bdf1-4680-853f-23c3a05756f5
-- title:
--   Lemma 7: determinant-one synthesis needs no ancilla
-- statement:
--   Let $U$ be a unitary operator on $n\ge0$ qubits with entries in $R=\mathbb Z[1/\sqrt2,i]$. If $\det U=1$, then
--
--   $$\exists C\text{ over }H,S,\mathrm{CNOT},T,\omega\text{ on }n\text{ wires},\qquad U_C=U.$$
--
--   No ancilla is used, and equality includes absolute phase. The entry-ring premise is part of the synthesis hypotheses of Theorem 1, as used in the proof of Lemma 7. This gives the determinant-one part of the ancilla-free characterization.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 6, Lemma 7: determinant-one synthesis needs no ancilla

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P85

open scoped Classical BigOperators

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega InDomega Residue bits residue residueMultiply Reducible)

open QAlgorithms.Papers.Independent.Support21.P13
  (synthesisRing integralRing coordinateValue HTLetter htWordMatrix EntriesInRing cliffordTLibrary)

local notation "omega" => QAlgorithms.gateT true true

local notation "sqrtTwo" => ((Real.sqrt 2 : ℝ) : ℂ)

/-- Lemma 7, PDF p.6: determinant-one ring unitaries require no ancilla. -/
theorem determinantOne_noAncilla (n : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (unitary : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (ring : EntriesInRing U)
    (determinant : U.det = 1) :
    ∃ c : Circuit gateSet n, c.unitary = U := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
