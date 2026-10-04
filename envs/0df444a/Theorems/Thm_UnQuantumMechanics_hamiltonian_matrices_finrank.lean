-- Prove2me | Theorems.Thm_UnQuantumMechanics_hamiltonian_matrices_finrank
-- name    : UnQuantumMechanics.hamiltonian_matrices_finrank
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T17:13:32.40431+00:00
-- url     : https://prove2.me/theorems/f4fc756a-9a11-4a6c-906f-82856066bf28
-- title:
--   Hamiltonian $2n\times 2n$ matrices form a space of dimension $n(2n+1)$
-- statement:
--   The real $2n\times 2n$ Hamiltonian matrices span a real vector space of dimension
--   $$\nu_s = n(2n+1).$$
--
--   **Formalization Note** "Number of linearly independent elements" is formalized as the dimension of the real linear span of the set of Hamiltonian $2n\times 2n$ matrices (which is in fact a linear subspace).
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI.B, p. 17, Eq. (55)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem hamiltonian_matrices_finrank (n : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ {M | IsHamiltonianMatrix n M}) = n * (2 * n + 1) := by sorry

end UnQuantumMechanics
