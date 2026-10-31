-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_globalSpectralPairing
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.globalSpectralPairing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:48:14.659136+00:00
-- url     : https://prove2.me/theorems/176a6467-76eb-4fed-919b-8642710f8939
-- title:
--   Global inversion and spectral multiplicities
-- statement:
--   Let $n\ge1$ and let $H$ be a Hermitian traceless $2^n\times2^n$ matrix. Write $m_H(\lambda)$ for the algebraic multiplicity of the real eigenvalue $\lambda$, with multiplicity zero for a non-eigenvalue. Then
--
--   $$\exists U\in\mathrm{SU}(2^n):\ UHU^\dagger=-H\quad\Longleftrightarrow\quad\forall\lambda\in\mathbb R,\ m_H(\lambda)=m_H(-\lambda).$$
--
--   The condition at zero is automatic. Thus the nonzero spectrum must occur in opposite-sign pairs, including multiplicities. This criterion concerns unrestricted unitary conjugation and supplies only a necessary condition when operations are restricted to local factors.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 3, Algebra I: global unitary inversion and eigenvalue pairing

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Algebra I, PDF pp.3–4: global SU conjugation iff positive/negative
real eigenvalues have matching multiplicities. Zeros need no restriction. -/
theorem globalSpectralPairing {n : ℕ} (hn : 0 < n) (H : Op (QAlgorithms.Qubits n))
    (hH : IsHamiltonian H) :
    (∃ U : Matrix.specialUnitaryGroup (QAlgorithms.Qubits n) ℂ,
      adjointConjugation (U : Op (QAlgorithms.Qubits n)) H = -H) ↔
    ∀ lam : ℝ, H.charpoly.roots.count (lam : ℂ) =
      H.charpoly.roots.count ((-lam : ℝ) : ℂ) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
