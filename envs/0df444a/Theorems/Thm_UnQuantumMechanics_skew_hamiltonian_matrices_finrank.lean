-- Prove2me | Theorems.Thm_UnQuantumMechanics_skew_hamiltonian_matrices_finrank
-- name    : UnQuantumMechanics.skew_hamiltonian_matrices_finrank
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T18:10:50.092763+00:00
-- url     : https://prove2.me/theorems/903964c3-cfc7-494a-a59d-1ac3ef5b8430
-- title:
--   Skew-Hamiltonian $2n\times 2n$ matrices form a space of dimension $n(2n-1)$
-- statement:
--   The real $2n\times 2n$ skew-Hamiltonian matrices span a real vector space of dimension
--   $$\nu_c = n(2n-1).$$
--
--   **Formalization Note** As for Eq. (55), the count is the dimension of the real linear span of the set of skew-Hamiltonian matrices. The factor $2n-1$ is computed in natural numbers; for $n = 0$ both sides are $0$, so truncated subtraction plays no role.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI.B, p. 17, Eq. (56)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem skew_hamiltonian_matrices_finrank (n : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ {M | IsSkewHamiltonianMatrix n M}) = n * (2 * n - 1) := by sorry

end UnQuantumMechanics
