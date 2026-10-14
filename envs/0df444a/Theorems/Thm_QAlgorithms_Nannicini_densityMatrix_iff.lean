-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_densityMatrix_iff
-- name    : QAlgorithms.Nannicini.densityMatrix_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:26.626246+00:00
-- url     : https://prove2.me/theorems/de26c53d-e5a6-4df4-a629-5221acfd6a93
-- title:
--   Density matrices are exactly the unit-trace positive semidefinite matrices
-- statement:
--   Let $\rho$ be a complex $2^q\times 2^q$ matrix acting on $q$ qubits. An ensemble of pure states is a family $\{p_j,|\psi_j\rangle\}_{j=1,\dots,m}$ of unit vectors $|\psi_j\rangle\in(\mathbb C^2)^{\otimes q}$ with probabilities $p_j\ge 0$, $\sum_j p_j=1$. Its density matrix is $\sum_j p_j|\psi_j\rangle\langle\psi_j|$ (Definition 1.55). Then
--
--   $$
--   \exists\, m,\ \{p_j,|\psi_j\rangle\}_{j=1}^m \text{ an ensemble with } \rho=\sum_{j=1}^m p_j|\psi_j\rangle\langle\psi_j| \iff \operatorname{Tr}\rho=1 \text{ and } \rho\succeq 0.
--   $$
--
--   This is the standard intrinsic description of mixed states. Later chapters use it to recognize a matrix as a quantum state without exhibiting an ensemble.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes Hermiticity.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 36, Theorem 1.60. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

open scoped ComplexOrder


/-- Nannicini p.36, Theorem 1.60 (characterization of density matrices): a `q`-qubit matrix `ρ`
is the density matrix `∑_j p_j |ψ_j⟩⟨ψ_j|` of some ensemble `{p_j, |ψ_j⟩}_{j=1..m}` of pure
states (unit vectors) with probabilities `p_j ≥ 0`, `∑_j p_j = 1`, for some `m`, if and only if
`ρ` has unit trace and is positive semidefinite. -/
theorem densityMatrix_iff {q : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) :
    (∃ (m : ℕ) (p : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ (Qubits q)),
        (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧ (∀ j, IsState (ψ j)) ∧ ρ = ensembleDensity p ψ) ↔
      ρ.trace = 1 ∧ ρ.PosSemidef := by sorry



end QAlgorithms.Nannicini
