-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_exactSynthesis
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.exactSynthesis
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:07:43.035634+00:00
-- url     : https://prove2.me/theorems/6ee8d826-ba18-4370-9971-183108fced9c
-- title:
--   Theorem 1: exact multiqubit Clifford+T synthesis with one clean ancilla
-- statement:
--   Let $U$ be a unitary operator on $n$ qubits, where $n\ge0$, and put $R=\mathbb Z[1/\sqrt2,i]$. Use exactly the elementary generators $H,S,\mathrm{CNOT},T,\omega$, with $\omega=e^{i\pi/4}$ available as a scalar gate. A clean ancilla starts and ends in $|0\rangle$ for every input vector. Then
--
--   $$
--   U\text{ has an exact circuit with finitely many clean ancillas}
--   \iff (\forall x,y,\ U_{xy}\in R).
--   $$
--
--   Whenever the entry condition holds, an exact circuit using at most one clean ancilla exists. Equality includes absolute phase. The circuit is chosen for the operator and works for every input vector.
--
--   This characterizes the matrices admitting exact multiqubit Clifford+T synthesis.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 1, Theorem 1: exact multiqubit Clifford+T synthesis with one clean ancilla

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

/-- Theorem 1, PDF pp.1,5: ring iff exact synthesis, with at most one clean ancilla. -/
theorem exactSynthesis (n : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (unitary : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ((∃ a : ℕ, ∃ c : Circuit gateSet (n + a), ImplementsWithCleanAncillas c.unitary U) ↔
      EntriesInRing U) ∧
    (EntriesInRing U → ∃ a : ℕ, a ≤ 1 ∧ ∃ c : Circuit gateSet (n + a),
      ImplementsWithCleanAncillas c.unitary U) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
