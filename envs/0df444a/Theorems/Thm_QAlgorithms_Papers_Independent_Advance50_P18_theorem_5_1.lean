-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_theorem_5_1
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.theorem_5_1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:48:07.288107+00:00
-- url     : https://prove2.me/theorems/f18ef54c-4960-4b06-bfb6-b94b937c19c7
-- title:
--   Theorem 5.1: no-ancilla key-entropy lower bound
-- statement:
--   Let an ancilla-free private quantum channel encrypt all unit $n$-qubit vectors to the fixed output $I_{2^n}/2^n$. Its $N$ key labels have probabilities $p_i\ge0$ summing to one, and its keyed operators $U_i$ are fixed unitaries. The Shannon entropy of the key in bits obeys
--
--   $$H(p_1,\ldots,p_N)\ge2n.$$
--
--   Zero-probability labels are allowed. This is the paper’s no-ancilla lower bound; no bound on individual probabilities is assumed.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 6, Theorem 5.1: no-ancilla key-entropy lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.6, Theorem 5.1: every ancilla-free full-source PQC with the displayed
maximally mixed output has Shannon key entropy at least 2n bits. -/
theorem theorem_5_1 (n N : ℕ) (E : KeyedUnitaryEnsemble (Fin N) (Qubits n))
    (h : BarePQC (allPure (Qubits n)) E (sourceMixedIdentity (Qubits n))) :
    2 * (n : ℝ) ≤ keyEntropy E.p := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
