-- Prove2me | Theorems.Thm_UnQuantumMechanics_skew_flow_conserves_hamiltonian
-- name    : UnQuantumMechanics.skew_flow_conserves_hamiltonian
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:12:55.418993+00:00
-- url     : https://prove2.me/theorems/d83a3ea5-6b75-4fc6-b3cd-fa9ea53a7acf
-- title:
--   The flow $\dot\psi = J\nabla H$ with $J$ skew-symmetric conserves $H$
-- statement:
--   Let $J$ be a real $\nu\times\nu$ skew-symmetric matrix and let $H:\mathbb R^\nu\to\mathbb R$ be differentiable (with no explicit time dependence). Let $\psi:\mathbb R\to\mathbb R^\nu$ be a differentiable curve satisfying
--   $$\dot\psi(\tau) = J\,\nabla_\psi H(\psi(\tau)) \quad\text{for all } \tau .$$
--   Then $H$ is a constant of motion:
--   $$\frac{d}{d\tau} H(\psi(\tau)) = 0 \quad \text{for all }\tau.$$
--
--   This is the paper's derivation of the general form of an equation of motion that conserves a given quantity $H$.
--
--   **Formalization Note** The $k$-th component of $\nabla_\psi H(x)$ is written as the derivative of $H$ at $x$ applied to the $k$-th standard basis vector.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. IV, p. 13, Eqs. (26)–(28)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem skew_flow_conserves_hamiltonian {ν : ℕ} (J : Matrix (Fin ν) (Fin ν) ℝ) (hJ : Jᵀ = -J)
    (Hf : (Fin ν → ℝ) → ℝ) (hHf : Differentiable ℝ Hf) (ψ : ℝ → Fin ν → ℝ)
    (hψ : ∀ τ, HasDerivAt ψ (J *ᵥ (fun k => fderiv ℝ Hf (ψ τ) (Pi.single k 1))) τ) :
    ∀ τ, HasDerivAt (fun t => Hf (ψ t)) 0 τ := by sorry

end UnQuantumMechanics
