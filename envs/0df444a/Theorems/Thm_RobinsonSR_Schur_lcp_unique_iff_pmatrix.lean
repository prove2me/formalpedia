-- Prove2me | Theorems.Thm_RobinsonSR_Schur_lcp_unique_iff_pmatrix
-- name    : RobinsonSR.Schur.lcp_unique_iff_pmatrix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:38.665971+00:00
-- url     : https://prove2.me/theorems/a934b4c7-7377-4329-a67d-b07ca44e9e50
-- title:
--   Linear complementarity has a unique solution for every input iff the matrix is a P-matrix
-- statement:
--   For a real square matrix $M$, the linear complementarity problem with input $z$ asks for $w\geq0$ such that $Mw-z\geq0$ and $w^\top(Mw-z)=0$. It has exactly one solution for every $z$ if and only if every nonempty principal minor of $M$ is positive:
--
--   $$
--   (\forall z\;\exists!w\geq0:\ Mw-z\geq0,\ w^\top(Mw-z)=0)
--   \quad\Longleftrightarrow\quad M\text{ is a P-matrix}.
--   $$
--
--   This is the complementarity characterization cited by Robinson for the nonnegative orthant case.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 52, (3.8) and citation [6]

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 52, citing [6], for the LCP (3.8). -/
theorem lcp_unique_iff_pmatrix (s : ℕ) (M : Matrix (Fin s) (Fin s) ℝ) :
    (∀ z : Fin s → ℝ, ∃! w : Fin s → ℝ,
      (∀ j, 0 ≤ (M.mulVec w - z) j) ∧
      (∀ j, 0 ≤ w j) ∧
      w ⬝ᵥ (M.mulVec w - z) = 0) ↔ IsPMatrix M := by sorry

end RobinsonSR.Schur
