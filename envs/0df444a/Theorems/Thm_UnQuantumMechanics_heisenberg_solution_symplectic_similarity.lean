-- Prove2me | Theorems.Thm_UnQuantumMechanics_heisenberg_solution_symplectic_similarity
-- name    : UnQuantumMechanics.heisenberg_solution_symplectic_similarity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:49:09.853487+00:00
-- url     : https://prove2.me/theorems/15714d90-c8fe-4916-8a3a-d498f337d0a0
-- title:
--   Solutions of $\dot S = [H,S]$ are symplectic similarity transforms
-- statement:
--   Let $H$ be a Hamiltonian $2n\times 2n$ matrix (constant in time) and let $S:\mathbb R\to\mathbb R^{2n\times2n}$ be differentiable at every time and satisfy Heisenberg's equation $\dot S = HS - SH$. Then for every $\tau$
--   $$S(\tau) = \exp(H\tau)\,S(0)\,\exp(-H\tau).$$
--
--   Since $\exp(H\tau)$ is symplectic (Eq. 50), this shows that time evolution acts on $S$ by symplectic similarity transformations.
--
--   **Formalization Note** Derivatives are entrywise; $\exp$ is the matrix exponential.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI, p. 17, Eq. (51)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem heisenberg_solution_symplectic_similarity (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hH : IsHamiltonianMatrix n H) (S : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hS : ∀ τ i j, HasDerivAt (fun t => S t i j) ((H * S τ - S τ * H) i j) τ) (τ : ℝ) :
    S τ = NormedSpace.exp (τ • H) * S 0 * NormedSpace.exp ((-τ) • H) := by sorry

end UnQuantumMechanics
