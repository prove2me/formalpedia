-- Prove2me | Theorems.Thm_UnQuantumMechanics_hamiltonian_transpose
-- name    : UnQuantumMechanics.hamiltonian_transpose
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T12:11:45.571637+00:00
-- url     : https://prove2.me/theorems/38fa7274-50b4-4ccf-b8e9-8948dde4f8bb
-- title:
--   Transpose of a Hamiltonian matrix: $H^T = \gamma_0 H \gamma_0$
-- statement:
--   Let $H = \gamma_0 A$ be a Hamiltonian $2n\times 2n$ matrix, $A$ symmetric. Then
--   $$H^T = \gamma_0 H \gamma_0 .$$
--
--   This identity is the algebraic characterization of Hamiltonian matrices used in the derivation of Heisenberg's equation (Eq. 42).
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. IV, p. 14, Eq. (36)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem hamiltonian_transpose (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H) :
    Hᵀ = gamma0 n * H * gamma0 n := by sorry

end UnQuantumMechanics
