-- Prove2me | Theorems.Thm_WeilConjectures_exists_similar_to_transpose
-- name    : WeilConjectures.exists_similar_to_transpose
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:07:08.383402+00:00
-- url     : https://prove2.me/theorems/d89cd3e7-e7b9-44e9-8b89-5a78a7667f4a
-- title:
--   Every Square Matrix over a Field Is Similar to Its Transpose
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. For every square matrix $A \in M_\iota(K)$ there exists a $K$-linear automorphism $P : K^\iota \xrightarrow{\sim} K^\iota$ of the standard coordinate space such that
--   $$P \circ A \circ P^{-1} = A^{\mathsf{T}},$$
--   i.e. $P.\mathrm{conj}(\mathtt{toLin}' A) = \mathtt{toLin}' A^{\mathsf{T}}$.
--
--   This is the classical statement that every matrix over a field is similar to its transpose (rational canonical form / invariant factors; Hoffman–Kunze, Bourbaki). It is the matrix-level child of `WeilConjectures.exists_linearEquiv_conj_eq_dualTranspose`, which transports the similarity along a finite basis and $\mathtt{Basis.toDualEquiv}$.
-- source:
--   Standard linear algebra: every matrix over a field is similar to its transpose (rational canonical form / invariant factors); cf. Hoffman–Kunze, Linear Algebra, Ch. 6; Bourbaki, Algèbre, Ch. VII

import Mathlib

/-- Every square matrix over a field is similar to its transpose: there exists a linear
automorphism `P` of the standard coordinate space such that
`P.conj (toLin' A) = toLin' Aᵀ`.

This is the classical rational-canonical / invariant-factor form of transpose similarity
(Hoffman–Kunze, Bourbaki). It is the matrix-level child of
`exists_linearEquiv_conj_eq_dualTranspose`, which transports the similarity along
`Basis.toDualEquiv`. -/

theorem WeilConjectures.exists_similar_to_transpose
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' A.transpose := by
  sorry
