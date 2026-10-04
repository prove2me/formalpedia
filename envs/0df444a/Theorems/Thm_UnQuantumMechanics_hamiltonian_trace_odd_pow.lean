-- Prove2me | Theorems.Thm_UnQuantumMechanics_hamiltonian_trace_odd_pow
-- name    : UnQuantumMechanics.hamiltonian_trace_odd_pow
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T15:21:04.88714+00:00
-- url     : https://prove2.me/theorems/98f94c6c-28a1-4300-ac52-f14faa85221b
-- title:
--   Odd powers of a Hamiltonian matrix are traceless
-- statement:
--   Let $S = \gamma_0 A$ be a Hamiltonian $2n\times 2n$ matrix ($A$ symmetric). Then every odd power of $S$ is traceless:
--   $$\operatorname{Tr}\big(S^{2k+1}\big) = 0\qquad (k = 0, 1, 2,\dots).$$
--
--   Consequently only the even powers in the Lax invariants (47) carry information.
--
--   **Formalization Note** The source phrases the hypothesis with $A$ symmetric positive definite; the statement here only assumes $A$ symmetric (the paper's definition of a Hamiltonian matrix). This is needed because the autocorrelation matrix $S = \Sigma\gamma_0^T$ equals $\gamma_0 A$ with $A = -\gamma_0^T\Sigma\gamma_0$, which is negative (not positive) definite when $\Sigma$ is positive definite.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI, p. 17, Eq. (48)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem hamiltonian_trace_odd_pow (n : ℕ) (S : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hS : IsHamiltonianMatrix n S) (k : ℕ) :
    (S ^ (2 * k + 1)).trace = 0 := by sorry

end UnQuantumMechanics
