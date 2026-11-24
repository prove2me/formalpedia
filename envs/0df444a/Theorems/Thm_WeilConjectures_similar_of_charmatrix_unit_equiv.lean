-- Prove2me | Theorems.Thm_WeilConjectures_similar_of_charmatrix_unit_equiv
-- name    : WeilConjectures.similar_of_charmatrix_unit_equiv
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:24:19.754809+00:00
-- url     : https://prove2.me/theorems/fde782ed-36c8-42e3-a89b-1bc2d05e88c4
-- title:
--   Similarity from Unit Equivalence of Characteristic Matrices
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. If $A,B \in M_\iota(K)$ have characteristic matrices that are equivalent over $K[X]$ — i.e. there exist unit-determinant $P,Q$ with
--   $$P\, \mathrm{charmatrix}(A)\, Q = \mathrm{charmatrix}(B),$$
--   then $A$ and $B$ are similar over $K$: there exists $P_0 \in \mathrm{GL}(K^\iota)$ with $P_0 A P_0^{-1} = B$ (equivalently $P_0.\mathrm{conj}(\mathrm{toLin}' A)=\mathrm{toLin}' B$).
--
--   This is the rational-canonical / invariant-factor uniqueness criterion (A41b).
-- source:
--   Matrix.charmatrix; LinearEquiv.conj; Hoffman–Kunze, Linear Algebra, Ch. 6–7

import Mathlib

/-- A41b: unit-equivalence of characteristic matrices over `K[X]` implies
similarity of the underlying matrices over `K`.

**REUSE:** `Matrix.charmatrix`, `LinearEquiv.conj`, `Matrix.toLin'`,
rational-canonical / invariant-factor uniqueness. -/

theorem WeilConjectures.similar_of_charmatrix_unit_equiv
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (h : ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * Matrix.charmatrix A * Q = Matrix.charmatrix B) :
    ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' B := by
  sorry
