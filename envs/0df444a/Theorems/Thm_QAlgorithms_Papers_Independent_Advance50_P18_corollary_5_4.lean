-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_corollary_5_4
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.corollary_5_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:50:10.175831+00:00
-- url     : https://prove2.me/theorems/f87e60b9-0a3c-4ad5-9970-b452e84a10f9
-- title:
--   Corollary 5.4: general mixed-ancilla quantum lower bound
-- statement:
--   Let a private quantum channel encrypt every unit $n$-qubit vector with $N$ key labels of probabilities $p_i$. Permit any finite number $a$ of ancillary qubits in an arbitrary fixed mixed state, arbitrary fixed full-space unitaries, and any constant full-output density. Then
--
--   $$H(p_1,\ldots,p_N)\ge2n,\qquad N\ge2^{2n}.$$
--
--   Entropy is measured in bits; zero-probability labels are permitted. Neither maximal mixing of the output nor purity of the ancilla is assumed. This is the lower bound that establishes optimality of the full quantum one-time pad.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 8, Corollary 5.4: general mixed-ancilla quantum lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.8, Corollary 5.4: arbitrary mixed ancillas cannot reduce the 2n-bit
entropy lower bound; the number of key labels is at least 2^(2n). -/
theorem corollary_5_4 (n a N : ℕ)
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ))
    (h : PQC (allPure (Qubits n)) E anc rho0) :
    2 * (n : ℝ) ≤ keyEntropy E.p ∧ 2 ^ (2 * n) ≤ N := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
