-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_example3_6_first
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.example3_6_first
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:19:03.736855+00:00
-- url     : https://prove2.me/theorems/da23f350-f6ff-4ba3-88ed-4dbb9b429157
-- title:
--   Two-sparse Pauli eigenspace states
-- statement:
--   Let $P_A$ be any nonidentity Pauli on $n$ qubits, and let $u\in\{+1,-1\}$. Then
--
--   $$\rho_u=\frac{I+uP_A}{2^n}$$
--
--   is a density matrix with exactly two nonzero Pauli coefficients. The matrix $\Pi_u=(I+uP_A)/2$ is the orthogonal projector onto the $u$ eigenspace, and $\rho_u=2^{1-n}\Pi_u$.
--
--   These examples supply the sparse input states used in channel-prediction lower bounds. The nonidentity hypothesis excludes the empty nonidentity sector at $n=0$.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 18, Example 3.6, first bullet: two-sparse Pauli eigenspace state

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.18, Example 3.6 first bullet: both signs, normalized density,
exactly two Pauli coefficients, and proportionality to the appropriate projector. -/
theorem example3_6_first {n : ℕ} (A : ErrorMitigation.PauliIndex n) (hA : A ≠ (fun _ => .I))
    (minus : Bool) :
    IsDensityMatrix (eigenspaceState A minus) ∧
    supportCount (ErrorMitigation.pauliStateVector (eigenspaceState A minus)) = 2 ∧
    let P : (Matrix (Qubits n) (Qubits n) ℂ) := (1/2 : ℂ) •
      (1 + (if minus then (-1 : ℂ) else 1) • pauliOps A)
    P.IsHermitian ∧ P * P = P ∧
    eigenspaceState A minus = ((2 : ℂ) / (2 : ℂ)^n) • P ∧
    LinearMap.range (Matrix.toLin' P) =
      LinearMap.ker (Matrix.toLin'
        (pauliOps A - (if minus then (-1 : ℂ) else 1) • (1 : (Matrix (Qubits n) (Qubits n) ℂ)))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
