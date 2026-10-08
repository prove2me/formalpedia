-- Prove2me | Theorems.Thm_SuttonTD_Convergence_theorem_A_3
-- name    : SuttonTD.Convergence.theorem_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:35.522227+00:00
-- url     : https://prove2.me/theorems/a90cec16-47c4-4c9b-baa5-350242d31043
-- title:
--   Theorem A.3 — $A$ positive definite iff $A+A^\top$ positive definite
-- statement:
--   Let $A$ be a real square matrix, and call a matrix positive definite if $y^\top My>0$ for every real $y\ne0$ (footnote 6; no symmetry required). Then
--
--   $$A \text{ is positive definite} \iff A+A^\top \text{ is positive definite}.$$
--
--   This lets the non-symmetric matrix $D(I-Q)$ be treated through its symmetric part.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, Appendix, Theorem A.3, p. 44 (PDF p. 36)

import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
open Matrix

namespace SuttonTD.Convergence

/-- **Theorem A.3** (Sutton 1988, Appendix, p. 44, PDF p. 36): "A square matrix `A` is positive
definite if and only if `A + Aᵀ` is positive definite."

Formalization Note: positive definite is the paper's footnote 6 (`yᵀAy > 0` for every real
`y ≠ 0`), `IsPosDefReal`, which does not require symmetry. -/
theorem theorem_A_3 {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
    IsPosDefReal A ↔ IsPosDefReal (A + Aᵀ) := by sorry

end SuttonTD.Convergence
