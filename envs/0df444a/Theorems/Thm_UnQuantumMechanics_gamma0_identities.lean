-- Prove2me | Theorems.Thm_UnQuantumMechanics_gamma0_identities
-- name    : UnQuantumMechanics.gamma0_identities
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:43:54.941994+00:00
-- url     : https://prove2.me/theorems/8f6c3754-cab7-4cad-8704-743ff429c443
-- title:
--   Identities of the symplectic unit matrix $\gamma_0$
-- statement:
--   Let $\gamma_0 = \mathbf 1_n\otimes\eta_0$ be the symplectic unit matrix for $n$ degrees of freedom. Then
--   1. $\gamma_0^T = -\gamma_0$,
--   2. $\gamma_0^2 = -\mathbf 1$,
--   3. $\gamma_0^T\gamma_0 = \mathbf 1$.
--
--   These identities are used throughout the paper to move $\gamma_0$ across products of Hamiltonian matrices.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. IV, p. 14, Eq. (33) and the text after it; text before Eq. (37); Sec. V, p. 15, text before Eq. (42)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem gamma0_identities (n : ℕ) :
    (gamma0 n)ᵀ = -gamma0 n ∧ gamma0 n * gamma0 n = -1 ∧ (gamma0 n)ᵀ * gamma0 n = 1 := by sorry

end UnQuantumMechanics
