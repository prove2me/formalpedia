-- Prove2me | Theorems.Thm_UnQuantumMechanics_skew_hamiltonian_transpose
-- name    : UnQuantumMechanics.skew_hamiltonian_transpose
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:25:27.527702+00:00
-- url     : https://prove2.me/theorems/5f9f2d8b-ce11-4e93-ac78-3078ff54af21
-- title:
--   Transpose of a skew-Hamiltonian matrix: $C^T = -\gamma_0 C \gamma_0$
-- statement:
--   Let $C = \gamma_0 B$ be a skew-Hamiltonian $2n\times 2n$ matrix, $B^T = -B$. Then
--   $$C^T = -\gamma_0 C\gamma_0 .$$
--
--   Together with Eq. (36) this distinguishes the two classes of matrices that make up the phase-space algebra.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI.B, p. 17, Eqs. (53)–(54)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem skew_hamiltonian_transpose (n : ℕ) (C : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hC : IsSkewHamiltonianMatrix n C) :
    Cᵀ = -(gamma0 n * C * gamma0 n) := by sorry

end UnQuantumMechanics
