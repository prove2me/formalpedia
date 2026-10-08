-- Prove2me | Theorems.Thm_SuttonTD_Convergence_theorem_A_2
-- name    : SuttonTD.Convergence.theorem_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:43.643999+00:00
-- url     : https://prove2.me/theorems/7e43867a-2214-4ff3-aca0-fef9afde9f56
-- title:
--   Theorem A.2 — $A^\top A$ is nonsingular when $A$ has linearly independent columns
-- statement:
--   Let $A$ be a real $m\times n$ matrix whose columns are linearly independent. Then the $n\times n$ matrix
--
--   $$A^\top A$$
--
--   is nonsingular. In the paper this gives the invertibility of $X^\top X$.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, Appendix, Theorem A.2, p. 44 (PDF p. 36)

import Mathlib
open Matrix

namespace SuttonTD.Convergence

/-- **Theorem A.2** (Sutton 1988, Appendix, p. 44, PDF p. 36): "For any matrix `A` with linearly
independent columns, `AᵀA` is nonsingular."

Formalization Note: `A` is an `m × n` real matrix; its columns are the vectors
`j ↦ (i ↦ A i j)`, and "nonsingular" is `IsUnit (Aᵀ * A)`. -/
theorem theorem_A_2 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ)
    (hA : LinearIndependent ℝ (fun j : n => fun i : m => A i j)) :
    IsUnit (Aᵀ * A) := by sorry

end SuttonTD.Convergence
