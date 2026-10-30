-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_corollary_5_5
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.corollary_5_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:50:46.606337+00:00
-- url     : https://prove2.me/theorems/7d0f1219-eeac-4c99-a66c-76acf19294a2
-- title:
--   Corollary 5.5: real product-state lower bound
-- statement:
--   Let $B=\{\cos\theta|0\rangle+\sin\theta|1\rangle:0\le\theta<2\pi\}$. Suppose a private quantum channel encrypts every vector of $B^{\otimes n}$, using $N$ keys with law $p_i$, arbitrary fixed complex unitaries, any fixed mixed ancillary register, and a constant full-output density. Then
--
--   $$H(p_1,\ldots,p_N)\ge n,\qquad N\ge2^n.$$
--
--   The restriction is on the promised input source, and does not constrain the encoding matrices to be real. This matches the key cost of independent uniform $I/Y$ conjugation.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 8, Corollary 5.5: real product-state lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.8, Corollary 5.5: real product sources require n bits of entropy and
at least 2^n key labels, allowing arbitrary complex unitaries and mixed ancillas. -/
theorem corollary_5_5 (n a N : ℕ)
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ))
    (h : PQC (realProductSource n) E anc rho0) :
    (n : ℝ) ≤ keyEntropy E.p ∧ 2 ^ n ≤ N := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
