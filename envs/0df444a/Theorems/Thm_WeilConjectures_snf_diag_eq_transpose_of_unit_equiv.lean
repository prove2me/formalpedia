-- Prove2me | Theorems.Thm_WeilConjectures_snf_diag_eq_transpose_of_unit_equiv
-- name    : WeilConjectures.snf_diag_eq_transpose_of_unit_equiv
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T02:13:05.312916+00:00
-- url     : https://prove2.me/theorems/2c951425-4642-4fd8-99c2-a5e515cae326
-- title:
--   SNF Diagonal Equals Its Transpose under Unit Equivalence
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ an assignment of diagonals to matrices over $K[X]$ that admits a Smith factorization $P M Q = \operatorname{diag}(d(M))$ with unit-determinant $P,Q$ for every $M$ (monic invariant-factor normalization). Then for every $M$ and index $i$,
--   $$d(M)(i) = d(M^{\mathsf{T}})(i).$$
--
--   This is uniqueness of invariant factors under transpose, via $(PMQ)^{\mathsf{T}} = Q^{\mathsf{T}} M^{\mathsf{T}} P^{\mathsf{T}}$ and self-transpose of diagonal matrices — no ad-hoc determinant expansions (A38/A42).
-- source:
--   Uniqueness of Smith invariant factors; Matrix.transpose_mul; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- Transpose invariance of SNF diagonals (A42 / A38): if `d` admits a Smith
factorization `P * M * Q = diagonal (d M)` for every `M` (monic invariant-factor
normalization), then `d M = d Mᵀ` pointwise.

Follows from uniqueness of invariant factors together with
`(P * M * Q)ᵀ = Qᵀ * Mᵀ * Pᵀ` and `diagonal(d)ᵀ = diagonal(d)` — no ad-hoc
determinant expansions.

**REUSE:** SNF uniqueness over Euclidean domains; `Matrix.transpose_mul`,
`Matrix.diagonal_transpose`, `Matrix.det_transpose` / `isUnit_det_transpose`. -/

theorem WeilConjectures.snf_diag_eq_transpose_of_unit_equiv
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hfac : ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M)) :
    ∀ M i, d M i = d M.transpose i := by
  sorry
