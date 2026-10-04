-- Prove2me | Theorems.Thm_UnQuantumMechanics_hamiltonian_skew_hamiltonian_algebra
-- name    : UnQuantumMechanics.hamiltonian_skew_hamiltonian_algebra
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T19:33:34.39148+00:00
-- url     : https://prove2.me/theorems/adcecda3-1371-41f7-9f84-bfab3f5d5b3b
-- title:
--   (Anti-)commutator table of Hamiltonian and skew-Hamiltonian matrices
-- statement:
--   Let $S_1, S_2$ be Hamiltonian and $C_1, C_2$ skew-Hamiltonian $2n\times 2n$ matrices, and let $k \in \mathbb N$. Then
--
--   1. $S_1S_2 - S_2S_1$, $\ C_1C_2 - C_2C_1$, $\ C_1S_1 + S_1C_1$ and $S_1^{2k+1}$ are Hamiltonian;
--   2. $S_1S_2 + S_2S_1$, $\ C_1C_2 + C_2C_1$, $\ C_1S_1 - S_1C_1$, $S_1^{2k}$ and $C_1^{k}$ are skew-Hamiltonian.
--
--   This is the "phase-space algebra" from which the paper later builds Clifford algebras.
--
--   **Formalization Note** In Eq. (57) the exponent letter $n$ is a generic natural number, not the number of degrees of freedom; it is written $k$ here. The case $k = 0$ is included, so in particular the identity matrix is skew-Hamiltonian.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI.B, pp. 17–18, Eq. (57)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem hamiltonian_skew_hamiltonian_algebra (n : ℕ) (S₁ S₂ C₁ C₂ : Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hS₁ : IsHamiltonianMatrix n S₁) (hS₂ : IsHamiltonianMatrix n S₂)
    (hC₁ : IsSkewHamiltonianMatrix n C₁) (hC₂ : IsSkewHamiltonianMatrix n C₂) (k : ℕ) :
    (IsHamiltonianMatrix n (S₁ * S₂ - S₂ * S₁) ∧
      IsHamiltonianMatrix n (C₁ * C₂ - C₂ * C₁) ∧
      IsHamiltonianMatrix n (C₁ * S₁ + S₁ * C₁) ∧
      IsHamiltonianMatrix n (S₁ ^ (2 * k + 1))) ∧
    (IsSkewHamiltonianMatrix n (S₁ * S₂ + S₂ * S₁) ∧
      IsSkewHamiltonianMatrix n (C₁ * C₂ + C₂ * C₁) ∧
      IsSkewHamiltonianMatrix n (C₁ * S₁ - S₁ * C₁) ∧
      IsSkewHamiltonianMatrix n (S₁ ^ (2 * k)) ∧
      IsSkewHamiltonianMatrix n (C₁ ^ k)) := by sorry

end UnQuantumMechanics
