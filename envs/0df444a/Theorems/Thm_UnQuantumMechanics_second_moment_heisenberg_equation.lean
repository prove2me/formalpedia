-- Prove2me | Theorems.Thm_UnQuantumMechanics_second_moment_heisenberg_equation
-- name    : UnQuantumMechanics.second_moment_heisenberg_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:24:37.434706+00:00
-- url     : https://prove2.me/theorems/1320e1f3-e946-498e-807e-d85e6883705d
-- title:
--   Second moments obey Heisenberg's equation $\dot S = [H, S]$
-- statement:
--   Let $H$ be a Hamiltonian $2n\times 2n$ matrix and let $\tau\mapsto\Sigma(\tau)$ be a matrix-valued function that, at the time $\tau$, is differentiable and satisfies the second-moment equation (40)
--   $$\dot\Sigma(\tau) = H\Sigma(\tau) + \Sigma(\tau)H^T .$$
--   Then the autocorrelation matrix $S(t) = \Sigma(t)\gamma_0^T$ is differentiable at $\tau$ and satisfies Heisenberg's equation (42)
--   $$\dot S(\tau) = H S(\tau) - S(\tau) H = [H, S(\tau)] .$$
--
--   **Formalization Note** Derivatives of matrix-valued functions are taken entrywise. $\Sigma$ is any matrix-valued function obeying Eq. (40); its interpretation as an ensemble average $\langle\psi\psi^T\rangle$ is not part of the statement.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. V, p. 15, Eqs. (40)–(42)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem second_moment_heisenberg_equation (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H)
    (Sig : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (τ : ℝ)
    (hSig : ∀ i j, HasDerivAt (fun t => Sig t i j) ((H * Sig τ + Sig τ * Hᵀ) i j) τ) :
    ∀ i j, HasDerivAt (fun t => autocorr n (Sig t) i j)
      ((H * autocorr n (Sig τ) - autocorr n (Sig τ) * H) i j) τ := by sorry

end UnQuantumMechanics
