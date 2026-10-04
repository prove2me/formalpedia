-- Prove2me | Theorems.Thm_UnQuantumMechanics_hamiltonian_flow_solution
-- name    : UnQuantumMechanics.hamiltonian_flow_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:44:10.813666+00:00
-- url     : https://prove2.me/theorems/3f55ab7c-fa71-4ade-83e0-a35ac1739511
-- title:
--   $\psi(\tau) = \exp(H\tau)\psi(0)$ solves $\dot\psi = H\psi$
-- statement:
--   Let $H$ be a Hamiltonian $2n\times 2n$ matrix and $\psi_0 \in \mathbb R^{2n}$. Then $\psi(\tau) = \exp(H\tau)\,\psi_0$ solves the linear Hamiltonian equation of motion (35):
--   $$\frac{d}{d\tau}\Big(\exp(H\tau)\,\psi_0\Big) = H\,\exp(H\tau)\,\psi_0 \qquad\text{for all }\tau\in\mathbb R .$$
--
--   **Formalization Note** $\exp$ is the matrix exponential (power series). Only the "is a solution" direction of Eq. (49) is stated; $\psi(0) = \psi_0$ holds since $\exp(0) = \mathbf 1$.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI, p. 17, Eq. (49) (solution of Eq. (35))

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem hamiltonian_flow_solution (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H)
    (ψ₀ : PhaseIdx n → ℝ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • H) *ᵥ ψ₀)
      (H *ᵥ (NormedSpace.exp (τ • H) *ᵥ ψ₀)) τ := by sorry

end UnQuantumMechanics
