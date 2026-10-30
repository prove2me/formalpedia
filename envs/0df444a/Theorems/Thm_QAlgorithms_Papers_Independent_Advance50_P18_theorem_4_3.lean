-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_theorem_4_3
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.theorem_4_3
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:47:04.017531+00:00
-- url     : https://prove2.me/theorems/f9c13803-2a4b-4787-8d1e-7695baae672c
-- title:
--   Theorem 4.3: when the constant output must be maximally mixed
-- statement:
--   Let $S$ be a set of unit $n$-qubit vectors and let $(p_i,U_i)$ be an ancilla-free private quantum channel with fixed output density $\rho_0$. Suppose that $I_{2^n}/2^n$ is a finite probability mixture of the projectors $|\psi\rangle\langle\psi|$ with $\psi\in S$. Then
--
--   $$\rho_0=I_{2^n}/2^n.$$
--
--   The mixture hypothesis concerns density matrices constructed from source vectors, rather than membership of a mixed density in a set of vectors. This identifies when the constant output of an ancilla-free channel is forced to be maximally mixed.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 5, Theorem 4.3: when the constant output must be maximally mixed

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.5, Theorem 4.3: without an ancilla, a maximally mixed source mixture
forces the fixed output to be maximally mixed. -/
theorem theorem_4_3 (n N : ℕ) (S : Set ((EuclideanSpace ℂ (Qubits n))))
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n)) (rho0 : (Matrix (Qubits n) (Qubits n) ℂ))
    (h : BarePQC S E rho0) (hmix : IsSourceMixture S (sourceMixedIdentity (Qubits n))) :
    rho0 = sourceMixedIdentity (Qubits n) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
