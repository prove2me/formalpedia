-- Prove2me | Theorems.Thm_UnQuantumMechanics_skew_symm_odd_zero_eigenvalue
-- name    : UnQuantumMechanics.skew_symm_odd_zero_eigenvalue
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T10:07:06.927649+00:00
-- url     : https://prove2.me/theorems/bd785b45-cdf1-4900-a5fa-09375869a7d2
-- title:
--   A skew-symmetric matrix of odd size has eigenvalue 0
-- statement:
--   Let $\nu$ be odd and let $J$ be a real $\nu\times\nu$ matrix with $J^T = -J$. Then $0$ is an eigenvalue of $J$: there is a nonzero $v \in \mathbb R^\nu$ with
--   $$J v = 0 .$$
--
--   In the paper this is the reason why a full-rank structure matrix requires an even number $\nu = 2n$ of dynamical variables.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. IV, p. 13, paragraph after Eq. (28)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem skew_symm_odd_zero_eigenvalue {ν : ℕ} (hν : Odd ν) (J : Matrix (Fin ν) (Fin ν) ℝ)
    (hJ : Jᵀ = -J) :
    Module.End.HasEigenvalue (Matrix.toLin' J) 0 := by sorry

end UnQuantumMechanics
