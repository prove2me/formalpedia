-- Prove2me | Theorems.Thm_RobinsonSR_NLP_pmatrix_iff_posdef_of_symm
-- name    : RobinsonSR.NLP.pmatrix_iff_posdef_of_symm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:12.799052+00:00
-- url     : https://prove2.me/theorems/dac5e8a4-723d-471c-85b5-319e58670a84
-- title:
--   Proof of Theorem 4.1, p. 56 — a symmetric matrix is a P-matrix iff it is positive definite
-- statement:
--   Let $M$ be a symmetric real square matrix indexed by a finite set. Then all principal minors of $M$ are positive if and only if $M$ is positive definite:
--   $$\det M_{JJ}>0\ \text{for every nonempty } J\quad\Longleftrightarrow\quad \langle w,Mw\rangle>0\ \text{for every } w\neq 0 .$$
--
--   In the proof of Theorem 4.1 this reduces the P-matrix requirement on the Schur complement (4.6) to positive definiteness.
--
--   **Formalization Note** Positive definiteness is stated without a symmetry clause (the paper's convention in §3); symmetry is the separate hypothesis. For an empty index set both sides hold vacuously.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 56, proof of Theorem 4.1; P-matrix defined p. 52

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Proof of Theorem 4.1, p. 56: a symmetric real matrix is a P-matrix (all principal minors
positive) if and only if it is positive definite. -/
theorem pmatrix_iff_posdef_of_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    IsPMatrix M ↔ RobinsonSR.Schur.PosDefNS M := by sorry

end RobinsonSR.NLP
