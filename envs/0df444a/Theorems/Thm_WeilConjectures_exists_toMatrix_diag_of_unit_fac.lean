-- Prove2me | Theorems.Thm_WeilConjectures_exists_toMatrix_diag_of_unit_fac
-- name    : WeilConjectures.exists_toMatrix_diag_of_unit_fac
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:31:59.605803+00:00
-- url     : https://prove2.me/theorems/3015ec0a-ff5a-4ec2-82da-c3c427042e65
-- title:
--   toMatrix Diagonal from Unit Factorization
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. Suppose $P,Q\in M_\iota(K[X])$ have unit determinants and $P M Q=\operatorname{diag}(a)$ for some family $a:\iota\to K[X]$. Then there exist bases of $K[X]^\iota$ in which $\mathrm{toLin}' M$ is represented by $\operatorname{diag}(a)$.
--
--   This is the converse change-of-basis to `exists_unit_cob_of_toMatrix_diagonal` (A64c).
-- source:
--   Pi.basisFun; Basis.map; Matrix.toLin'; Hoffman–Kunze Ch. 6

import Mathlib

/-- A64c REV-COB: unit-determinant factorization `P M Q = diag(a)` yields bases of
`K[X]^ι` in which `toLin' M` is represented by `diag(a)`.

Converse direction to `exists_unit_cob_of_toMatrix_diagonal` (503effa6).

**REUSE:** `Pi.basisFun`, `Basis.map`, `Matrix.toLin'`, `LinearMap.toMatrix`,
`Matrix.isUnit_iff_isUnit_det`. -/

theorem WeilConjectures.exists_toMatrix_diag_of_unit_fac
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι (Polynomial K)} {a : ι → Polynomial K}
    {P Q : Matrix ι ι (Polynomial K)}
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : P * M * Q = Matrix.diagonal a) :
    ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal a := by
  sorry
