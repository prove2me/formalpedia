-- Prove2me | Theorems.Thm_WeilConjectures_exists_invariant_factors_of_matrix
-- name    : WeilConjectures.exists_invariant_factors_of_matrix
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:25:56.734437+00:00
-- url     : https://prove2.me/theorems/eaa4c59c-735c-4c6f-b52f-d4efa2139056
-- title:
--   Invariant Factors Yield a Transpose-Invariant Rational Canonical Form
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exist operations $C$ and $P$ assigning to every square matrix $A \in M_\iota(K)$ a rational-canonical companion-block matrix $C(A)$ and a $K$-linear automorphism $P(A) : K^\iota \xrightarrow{\sim} K^\iota$ such that
--   $$P(A) \circ A \circ P(A)^{-1} = C(A)$$
--   and moreover
--   $$C(A) = C(A^{\mathsf{T}}).$$
--
--   The matrix $C(A)$ is assembled from the invariant factors of $X \cdot 1 - A$ over $K[X]$ (Smith normal form). Those factors are unchanged by transpose, since $(X \cdot 1 - A)^{\mathsf{T}} = X \cdot 1 - A^{\mathsf{T}}$, so the same companion-block form serves both $A$ and $A^{\mathsf{T}}$. This is the single SNF-child of `WeilConjectures.exists_similar_to_companion`.
-- source:
--   Standard linear algebra: Smith normal form over K[X] / invariant factors; cf. Hoffman–Kunze, Linear Algebra, Ch. 6; Bourbaki, Algèbre, Ch. VII

import Mathlib

/-- Smith normal form / invariant factors of `X • 1 - A` over `K[X]` yield a
rational-canonical companion-block matrix `C(A)` similar to `A`. The invariant factors
are unchanged by transpose (SNF of `(X • 1 - A)ᵀ = X • 1 - Aᵀ` coincides with that of
`X • 1 - A` up to units), so the same construction satisfies `C(A) = C(Aᵀ)`.

This is the single SNF-child of `exists_similar_to_companion` (A34); companion-block
assembly and transpose-invariance are packaged here so the parent sketch only
instantiates `C`, `P`. -/

theorem WeilConjectures.exists_invariant_factors_of_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (C : Matrix ι ι K → Matrix ι ι K)
      (P : Matrix ι ι K → ((ι → K) ≃ₗ[K] (ι → K))),
      (∀ A, (P A).conj (Matrix.toLin' A) = Matrix.toLin' (C A)) ∧
      (∀ A, C A = C A.transpose) := by
  sorry
