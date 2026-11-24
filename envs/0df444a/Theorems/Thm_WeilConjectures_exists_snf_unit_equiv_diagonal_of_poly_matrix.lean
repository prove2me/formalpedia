-- Prove2me | Theorems.Thm_WeilConjectures_exists_snf_unit_equiv_diagonal_of_poly_matrix
-- name    : WeilConjectures.exists_snf_unit_equiv_diagonal_of_poly_matrix
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:13:06.177714+00:00
-- url     : https://prove2.me/theorems/69103732-2eaf-4a07-9c47-ee8aa5782acb
-- title:
--   Unit Equivalence to SNF Diagonal over $K[X]$
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exists an assignment $d$ sending each matrix $M \in M_\iota(K[X])$ to a diagonal $d(M) : \iota \to K[X]$ such that $M$ is equivalent over $K[X]$ to that diagonal: there exist $P,Q$ with unit determinant satisfying
--   $$P\, M\, Q = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   This is the constructive Smith factorization over the Euclidean domain $K[X]$, lifted from Mathlib's `Submodule.smithNormalForm` / `smithNormalFormCoeffs` via `Polynomial.instEuclideanDomain` (A42 unit-equivalence phase).
-- source:
--   Smith normal form over Euclidean domains; Mathlib Submodule.smithNormalForm / smithNormalFormCoeffs; Polynomial.instEuclideanDomain; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- Smith factorization over `Polynomial K` (A42): an assignment `d` of diagonals such that
every matrix is unit-equivalent to `diagonal (d M)`.

Obtained by PID-lift of `Submodule.smithNormalForm` / `smithNormalFormCoeffs` along
`Polynomial.instEuclideanDomain`, reading the change-of-basis matrices as `P, Q`.

**REUSE:** `Submodule.smithNormalForm`, `Module.Basis.SmithNormalForm`,
`smithNormalFormCoeffs`, `Polynomial.instEuclideanDomain`,
`EuclideanDomain.to_principal_ideal_domain`. -/

theorem WeilConjectures.exists_snf_unit_equiv_diagonal_of_poly_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M) := by
  sorry
