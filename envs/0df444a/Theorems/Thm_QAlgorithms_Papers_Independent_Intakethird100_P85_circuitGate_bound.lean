-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_circuitGate_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.circuitGate_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:16:24.166326+00:00
-- url     : https://prove2.me/theorems/942452bf-5a75-4c88-aa72-248a9848c561
-- title:
--   §7, unnumbered: constructed one-ancilla circuit size
-- statement:
--   There are absolute positive constants $B,C$ such that the following holds. Let $n,k\ge1$ and let $U$ be a unitary $n$-qubit operator over $\mathbb Z[1/\sqrt2,i]$ with least complex-matrix denominator exponent $k$. The column-elimination trace and its elementary compilation return a circuit $A$ using one trailing clean helper, with
--
--   $$U_A(\psi\otimes|0\rangle)=(U\psi)\otimes|0\rangle\quad\text{for every }\psi,
--   \qquad |A|\le C3^{2^n}nk.$$
--
--   Each compiled one-/two-level operation contributes an actual segment of at most $Bn$ elementary gates, and the trace concatenates those segments. The count is over $H,S,\mathrm{CNOT},T,\omega$. This is an output-size bound for the constructed exact circuit, not an arithmetic runtime or optimality assertion.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 7, §7, unnumbered: constructed one-ancilla circuit size

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

/-- Section 7, PDF p.7: actual one-helper elementary output has O(3^(2^n) n k) gates.
The matrix-reduction and per-operation compilation traces tie the count to the output. -/
theorem circuitGate_bound :
    ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
    ∀ (n : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ) (k : ℕ),
      0 < n → 0 < k → U ∈ Matrix.unitaryGroup (Qubits n) ℂ → EntriesInRing U →
      LeastMatrixExponent U k →
      ∃ w : List (LevelOp (2 ^ n)), ∃ c : Circuit gateSet (n + 1),
        MatrixTrace (indexedMatrix U) k w ∧
        CompilationTrace B n (inverseWord w) c ∧
        ImplementsWithCleanAncillas c.unitary U ∧
        c.size ≤ C * 3 ^ (2 ^ n) * n * k := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
