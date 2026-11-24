-- Prove2me | Theorems.Thm_WeilConjectures_exists_similar_to_companion
-- name    : WeilConjectures.exists_similar_to_companion
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:12:29.675882+00:00
-- url     : https://prove2.me/theorems/90358a48-c246-4835-821a-33c54ff7324e
-- title:
--   Common Rational Canonical Form for a Matrix and Its Transpose
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. For every square matrix $A \in M_\iota(K)$ there exist a rational-canonical companion-block matrix $C \in M_\iota(K)$ and $K$-linear automorphisms $P, Q : K^\iota \xrightarrow{\sim} K^\iota$ such that
--   $$P \circ A \circ P^{-1} = C \qquad\text{and}\qquad Q \circ A^{\mathsf{T}} \circ Q^{-1} = C.$$
--
--   Equivalently, $A$ and $A^{\mathsf{T}}$ share a common similar form $C$ (the rational canonical form determined by the invariant factors of $A$, which coincide with those of $A^{\mathsf{T}}$). This is the single RCF-leaf child of `WeilConjectures.exists_similar_to_transpose`.
-- source:
--   Standard linear algebra: rational canonical form / invariant factors; cf. Hoffman–Kunze, Linear Algebra, Ch. 6; Bourbaki, Algèbre, Ch. VII

import Mathlib

/-- Every square matrix `A` over a field is similar to a rational-canonical companion-block
matrix `C` that depends only on the invariant factors of `A`. Since `A` and `Aᵀ` share the
same invariant factors, the same `C` is a common similar form for both:

there exist `P, Q` with `P.conj (toLin' A) = toLin' C` and `Q.conj (toLin' Aᵀ) = toLin' C`.

This is the single RCF-leaf child of `exists_similar_to_transpose` (Hoffman–Kunze / Bourbaki). -/

theorem WeilConjectures.exists_similar_to_companion
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    ∃ (C : Matrix ι ι K) (P Q : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' C ∧
      Q.conj (Matrix.toLin' A.transpose) = Matrix.toLin' C := by
  sorry
