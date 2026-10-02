-- Prove2me | Theorems.Thm_UnQuantumMechanics_skew_symm_eigenvalue_neg
-- name    : UnQuantumMechanics.skew_symm_eigenvalue_neg
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T09:02:15.639182+00:00
-- url     : https://prove2.me/theorems/3603389e-69b2-4a0b-8dfd-8fe1942e628f
-- title:
--   Eigenvalues of a real skew-symmetric matrix come in pairs ±λ
-- statement:
--   Let $J$ be a real $\nu \times \nu$ skew-symmetric matrix, $J^T = -J$. Regard $J$ as a complex matrix. If $\mu \in \mathbb C$ is an eigenvalue of $J$, then so is $-\mu$:
--   $$\mu \in \operatorname{spec}_{\mathbb C}(J) \implies -\mu \in \operatorname{spec}_{\mathbb C}(J).$$
--
--   The paper uses this pairing to argue that a skew-symmetric "structure matrix" of odd size must be singular, which forces an even number of dynamical variables.
--
--   **Formalization Note** Eigenvalues are taken over $\mathbb C$ for the complexified matrix, since a real skew-symmetric matrix generally has no real eigenvalues other than $0$.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. IV, p. 13, paragraph after Eq. (28)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem skew_symm_eigenvalue_neg {ν : ℕ} (J : Matrix (Fin ν) (Fin ν) ℝ) (hJ : Jᵀ = -J)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' (J.map (algebraMap ℝ ℂ))) μ) :
    Module.End.HasEigenvalue (Matrix.toLin' (J.map (algebraMap ℝ ℂ))) (-μ) := by sorry

end UnQuantumMechanics
