-- Prove2me | Theorems.Thm_WeilConjectures_exists_snf_diag_factorization_of_poly_matrix
-- name    : WeilConjectures.exists_snf_diag_factorization_of_poly_matrix
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:03:34.690601+00:00
-- url     : https://prove2.me/theorems/731581ee-379c-472f-b889-0fdd97ebde3f
-- title:
--   SNF Factorization over $K[X]$ with Transpose-Invariant Diagonal
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exists an assignment $d$ sending each matrix $M \in M_\iota(K[X])$ to a diagonal $d(M) : \iota \to K[X]$ such that
--   $$d(M)(i) = d(M^{\mathsf{T}})(i) \quad \text{for all } i,$$
--   and $M$ is equivalent over $K[X]$ to that diagonal: there exist $P,Q$ with unit determinant satisfying
--   $$P\, M\, Q = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   This is the PID-lift of Mathlib's `Submodule.smithNormalForm` along `Polynomial.instEuclideanDomain` (A40 extract / A37 PID-lift), packaging transpose-invariant Smith coefficients with an explicit factorization.
-- source:
--   Smith normal form over Euclidean domains; Mathlib Submodule.smithNormalForm / Module.Basis.SmithNormalForm; Polynomial.instEuclideanDomain; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- PID-lifted Smith normal form over `Polynomial K`: a diagonal assignment `d` together
with unit-determinant equivalences realizing `P * M * Q = diagonal (d M)`, and with
`d M = d Mᵀ` pointwise (A40 SNF-DIAG-SPLIT / A37 PID-LIFT).

**REUSE:** `Submodule.smithNormalForm`, `Module.Basis.SmithNormalForm`,
`Polynomial.instEuclideanDomain`, `EuclideanDomain.to_principal_ideal_domain`,
`Matrix.charmatrix_transpose`. -/

theorem WeilConjectures.exists_snf_diag_factorization_of_poly_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M)) := by
  sorry
