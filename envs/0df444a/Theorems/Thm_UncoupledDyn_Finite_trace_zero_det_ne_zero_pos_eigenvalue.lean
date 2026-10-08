-- Prove2me | Theorems.Thm_UncoupledDyn_Finite_trace_zero_det_ne_zero_pos_eigenvalue
-- name    : UncoupledDyn.Finite.trace_zero_det_ne_zero_pos_eigenvalue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:07:51.684984+00:00
-- url     : https://prove2.me/theorems/3f5ea904-bb13-4148-9de0-5d1ec194fb08
-- title:
--   §III, p. 1833 and fn. 15 — a real 3×3 matrix with zero trace and nonzero determinant has an eigenvalue with positive real part
-- statement:
--   Let $M$ be a real $3\times 3$ matrix with
--   $$\operatorname{tr} M=0\qquad\text{and}\qquad \det M\neq 0 .$$
--   Then $M$ has a complex eigenvalue $\lambda$ with $\operatorname{Re}\lambda>0$.
--
--   In the proof of Theorem 1 this turns the vanishing trace of the Jacobian into the failure of asymptotic stability, since hyperbolicity (in fact $\det J\ne 0$) is part of the Nash-convergence requirement.
--
--   **Formalization Note.** Eigenvalues are the elements of the spectrum of $M$ regarded as a complex matrix.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1833, §III, proof of Theorem 1 and fn. 15

import Mathlib

namespace UncoupledDyn.Finite

theorem trace_zero_det_ne_zero_pos_eigenvalue (M : Matrix (Fin 3) (Fin 3) ℝ)
    (htr : M.trace = 0) (hdet : M.det ≠ 0) :
    ∃ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), 0 < z.re := by sorry

end UncoupledDyn.Finite
