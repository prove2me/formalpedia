-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemma6_2
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemma6_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:09:48.029287+00:00
-- url     : https://prove2.me/theorems/5dcebbea-b28e-42d8-8a1b-8cbabdcf7a51
-- title:
--   Uniform bounds on derivatives of Hamiltonian Pauli expectations
-- statement:
--   Let $H=H^\dagger$ be an $n$-qubit Hamiltonian with its identity coefficient fixed to zero, $\rho$ any density matrix, and $P_B$ any Pauli string. Define $\mathcal U_t(\rho)=e^{-itH}\rho e^{itH}$. For every integer $k\ge0$ and $\tau\ge0$,
--
--   $$\left|\left.\frac{d^k}{dt^k}\operatorname{tr}\bigl(P_B\mathcal U_t(\rho)\bigr)\right|_{t=\tau}\right|\le(2\|H\|_\infty)^k.$$
--
--   This controls derivative errors in polynomial interpolation. At $k=0$ the right side is one, including $H=0$; for $k>0$, $H=0$ gives a zero derivative.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 29, Lemma 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.29-30, Lemma 6.2. Absolute value surrounds the derivative.
At k=0 this is the Pauli expectation bound; no positive norm assumption is needed. -/
theorem lemma6_2 {n : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian)
    (hidentity : hamiltonianCoeff H (fun _ => .I) = 0)
    (B : ErrorMitigation.PauliIndex n) (rho : (Matrix (Qubits n) (Qubits n) ℂ)) (hrho : IsDensityMatrix rho)
    (k : ℕ) (tau : ℝ) (htau : 0 ≤ tau) :
    |iteratedDeriv k (fun t : ℝ => (pauliOps B * hamiltonianDensityFlow H t rho).trace.re) tau| ≤
      (2 * specNorm H)^k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
