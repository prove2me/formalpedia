-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_theorem_5_3
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.theorem_5_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:49:33.297177+00:00
-- url     : https://prove2.me/theorems/19c9cea3-6ab2-4983-ad83-39022ec295a3
-- title:
--   Theorem 5.3: classical-message PQC key-entropy lower bound
-- statement:
--   Let a private quantum channel securely transmit every computational-basis state of an $m$-qubit register. It uses $N$ classical keys with fixed law $p_i$, fixed full-space unitaries, an arbitrary fixed mixed $a$-qubit ancilla, and a constant full-output density. Then its key entropy in bits satisfies
--
--   $$H(p_1,\ldots,p_N)\ge m.$$
--
--   The ancilla is transmitted with the encoding, and every key admits exact unitary inversion. Privacy is required for basis messages; no privacy assumption is imposed on their superpositions. This is the classical-message lower bound in the paper’s one-way quantum model.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 8, Theorem 5.3: classical-message PQC key-entropy lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.8, Theorem 5.3 (introduced on p.7): m-bit computational-basis messages
require at least m bits of Shannon key entropy, even with an arbitrary mixed ancilla. -/
theorem theorem_5_3 (m a N : ℕ)
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits m × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits m × Qubits a) (Qubits m × Qubits a) ℂ))
    (h : PQC (classicalSource (Qubits m)) E anc rho0) :
    (m : ℝ) ≤ keyEntropy E.p := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
