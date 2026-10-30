-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemma6_1
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemma6_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:09:04.125093+00:00
-- url     : https://prove2.me/theorems/1620a374-b46a-4081-a5cf-33af586ceb2a
-- title:
--   A sparse input isolates a Hamiltonian coefficient
-- statement:
--   Let $H=H^\dagger$ be an $n$-qubit Hamiltonian, with $\alpha(C)=2^{-n}\operatorname{tr}(HP_C)\in\mathbb R$ and the identity coefficient fixed to zero. Let $A$ have $A_j\ne I$ at a site $j$, and choose $b\in\{X,Y,Z\}\setminus\{A_j\}$. Let $B_j=b$ and $B_k=I$ for $k\ne j$. The constructed matrix
--
--   $$\rho=2^{-n}\left(I+\frac{i}{2}[P_A,P_B]\right)$$
--
--   is a density matrix and satisfies
--
--   $$\operatorname{tr}\bigl(P_B(-i[H,\rho])\bigr)=2\alpha(A).$$
--
--   This identifies an individual Hamiltonian coefficient in a short-time derivative. The paper credits the underlying observation to HKT21, Yu+23, Sti+22 and GCC22.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 29, Lemma 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.29, Lemma 6.1. The printed Ai and k!=i are corrected to Aj and
k!=j. The formula includes the constructed density matrix, not an assumed one.
The observation is attributed locally to HKT21, Yu+23, Sti+22, and GCC22. -/
theorem lemma6_1 {n : ℕ} (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian)
    (hidentity : hamiltonianCoeff H (fun _ => .I) = 0)
    (A : ErrorMitigation.PauliIndex n) (j : Fin n) (hA : A j ≠ .I)
    (b : Stabilizer.Pauli) (hb : b ≠ .I) (hbA : b ≠ A j) :
    IsDensityMatrix (pauliCoefficientProbe A (singleSite j b)) ∧
    (pauliOps (singleSite j b) *
      ((-Complex.I) • (H * pauliCoefficientProbe A (singleSite j b) - pauliCoefficientProbe A (singleSite j b) * H))).trace =
      ((2 * hamiltonianCoeff H A : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
