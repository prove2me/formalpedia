-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_theorem_4_1
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.theorem_4_1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:45:54.655983+00:00
-- url     : https://prove2.me/theorems/c073fe80-c96c-4b8c-bf4b-c5d3a21d5687
-- title:
--   Theorem 4.1: full tensor-Pauli private channel
-- statement:
--   Let $n\ge0$ and let $\sigma_0=I$, $\sigma_1=X$, $\sigma_2=Y$, and $\sigma_3=Z$. For $x\in\{0,1,2,3\}^n$, set $\bar\sigma_x=\bigotimes_{j=1}^n\sigma_{x_j}$. The fixed, ancilla-free encoder that chooses $x$ uniformly and applies $\bar\sigma_x$ is a private quantum channel on all unit $n$-qubit vectors. In particular,
--
--   $$\sum_{x\in\{0,1,2,3\}^n}2^{-2n}\bar\sigma_x|\psi\rangle\langle\psi|\bar\sigma_x^\dagger=I_{2^n}/2^n\quad(\|\psi\|=1).$$
--
--   The source’s Kraus coefficient is $2^{-n}$; its square is the key probability $2^{-2n}$. Each keyed unitary can be inverted exactly. This is the full quantum one-time pad.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 5, Theorem 4.1: full tensor-Pauli private channel

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.5, Theorem 4.1: the uniform full tensor-Pauli ensemble is a PQC. -/
theorem theorem_4_1 (n : ℕ) :
    BarePQC (allPure (Qubits n)) (fullPauli n) (sourceMixedIdentity (Qubits n)) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
