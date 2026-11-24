-- Prove2me | Theorems.Thm_WeilConjectures_similar_of_snf_diag_eq_on_charmatrix
-- name    : WeilConjectures.similar_of_snf_diag_eq_on_charmatrix
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T02:03:33.204993+00:00
-- url     : https://prove2.me/theorems/0526f45b-61c7-478b-a02c-06ba6e25e33a
-- title:
--   Similarity from Equal SNF Diagonals on Characteristic Matrices
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ an assignment of diagonals to matrices over $K[X]$ that admits a Smith factorization $P M Q = \operatorname{diag}(d(M))$ with unit-determinant $P,Q$ for every $M$. If $A,B \in M_\iota(K)$ satisfy
--   $$d(\mathrm{charmatrix}\, A) = d(\mathrm{charmatrix}\, B),$$
--   then $A$ and $B$ are similar: there exists $P \in \mathrm{GL}(K^\iota)$ with $P A P^{-1} = B$.
--
--   This is the invariant-factor / rational-canonical uniqueness criterion (A41), used as the classification phase of `WeilConjectures.exists_snf_diagonal_of_pid_matrix`.
-- source:
--   Rational canonical form uniqueness via invariant factors; Hoffman–Kunze, Linear Algebra, Ch. 6; cf. Matrix.charmatrix in Mathlib

import Mathlib

/-- Similarity classification from equal SNF diagonals on characteristic matrices (A41).
If `d` admits a Smith factorization `P * M * Q = diagonal (d M)` for every polynomial
matrix `M`, then equal `d` on `charmatrix A` and `charmatrix B` implies `A ∼ B`.

**REUSE:** rational-canonical / invariant-factor uniqueness over `K[X]`;
`Matrix.charmatrix`, `LinearEquiv.conj`. -/

theorem WeilConjectures.similar_of_snf_diag_eq_on_charmatrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hfac : ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M))
    {A B : Matrix ι ι K}
    (h : d (Matrix.charmatrix A) = d (Matrix.charmatrix B)) :
    ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' B := by
  sorry
