-- Prove2me | Theorems.Thm_WeilConjectures_exists_snf_diagonal_of_pid_matrix
-- name    : WeilConjectures.exists_snf_diagonal_of_pid_matrix
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:51:29.185356+00:00
-- url     : https://prove2.me/theorems/a400fb19-2bae-469f-9177-5ebd83cb9c04
-- title:
--   SNF Diagonal over $K[X]$ with Similarity Classification
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exists an assignment $\mathrm{diag}$ sending each matrix $M \in M_\iota(K[X])$ to its monic Smith-normal-form invariant-factor list such that
--   $$\mathrm{diag}(M) = \mathrm{diag}(M^{\mathsf{T}})$$
--   and moreover matrices over $K$ with the same invariant factors on their characteristic matrices are similar: if $\mathrm{diag}(\mathrm{charmatrix}\, A) = \mathrm{diag}(\mathrm{charmatrix}\, B)$, then $A \sim B$.
--
--   This is the PID-lift of Mathlib's `Submodule.smithNormalForm` along `Polynomial.instEuclideanDomain`, packaging SNF diagonal extraction and similarity classification for the parent `WeilConjectures.exists_snf_of_polynomial_matrix` (A39 phase 1).
-- source:
--   Smith normal form over Euclidean domains; Mathlib Submodule.smithNormalForm / Module.Basis.SmithNormalForm; Polynomial.instEuclideanDomain; cf. Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- Smith normal form diagonal for matrices over `Polynomial K`, obtained by PID-lift of
Mathlib `Submodule.smithNormalForm` / `Module.Basis.SmithNormalForm` along
`Polynomial.instEuclideanDomain` (`EuclideanDomain.to_principal_ideal_domain`).

Returns a transpose-invariant invariant-factor assignment `diag`, together with the
similarity-classification principle: matrices with the same `diag` on their
characteristic matrices are similar. (Companion-block assembly `rcf`/`sim` is then a
short choice-of-representatives argument in the parent sketch — A39 phase 2.)

**REUSE (A37):** `Submodule.smithNormalForm`, `Module.Basis.SmithNormalForm`,
`Polynomial.instEuclideanDomain`, `EuclideanDomain.to_principal_ideal_domain`,
`Matrix.charmatrix_transpose`. -/

theorem WeilConjectures.exists_snf_diagonal_of_pid_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (diag : Matrix ι ι (Polynomial K) → List (Polynomial K)),
      (∀ M, diag M = diag M.transpose) ∧
      (∀ A B : Matrix ι ι K,
        diag (Matrix.charmatrix A) = diag (Matrix.charmatrix B) →
        ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
          P.conj (Matrix.toLin' A) = Matrix.toLin' B) := by
  sorry
