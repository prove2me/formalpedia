-- Prove2me | Theorems.Thm_WeilConjectures_exists_unit_cob_of_toMatrix_diagonal
-- name    : WeilConjectures.exists_unit_cob_of_toMatrix_diagonal
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:18:51.576808+00:00
-- url     : https://prove2.me/theorems/503effa6-346f-4a0f-96ab-9b243b1aca18
-- title:
--   Unit Change-of-Basis from Diagonal toMatrix Representation
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ an assignment of diagonals to matrices over $K[X]$ such that for every $M$ there exist bases in which $\mathrm{toLin}' M$ is represented by $\operatorname{diag}(d(M))$. Then there exist unit-determinant change-of-basis matrices $P,Q$ with
--   $$P\, M\, Q = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   Construct $P,Q$ via `Basis.toMatrix` against the standard basis (A45 COB-FROM-BASIS); `IsUnit` of the determinants follows from basis invertibility.
-- source:
--   Basis.toMatrix change-of-basis; Matrix.isUnit_iff_isUnit_det; Mathlib LinearAlgebra.Matrix.Basis

import Mathlib

/-- A45 COB-FROM-BASIS: if `toLin' M` is diagonal in bases `bSrc`, `bTgt`, then there
exist unit-determinant change-of-basis matrices `P, Q` with
`P * M * Q = diagonal (d M)`.

Construct `P, Q` via `Basis.toMatrix` against the standard `Pi.basisFun` (no ad-hoc
entry formulas); `IsUnit det` from basis invertibility / `isUnit_iff_isUnit_det`.

**REUSE:** `Basis.toMatrix`, `LinearMap.toMatrix`, `Matrix.toLin'`,
`Pi.basisFun`, `Matrix.isUnit_iff_isUnit_det`. -/

theorem WeilConjectures.exists_unit_cob_of_toMatrix_diagonal
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hdiag : ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M)) :
    ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M) := by
  sorry
