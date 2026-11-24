-- Prove2me | Theorems.Thm_WeilConjectures_exists_snf_of_polynomial_matrix
-- name    : WeilConjectures.exists_snf_of_polynomial_matrix
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:42:51.154987+00:00
-- url     : https://prove2.me/theorems/f03c3514-0926-48f7-9096-a06d791d856e
-- title:
--   Smith Normal Form over $K[X]$ with Transpose-Invariant Factors
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exist operations assigning to every square matrix $M \in M_\iota(K[X])$ its monic invariant-factor list $\mathrm{invFactors}(M)$, a companion-block constructor $\mathrm{rcf}$ over $K$, and similarities $\mathrm{sim}(A)$ for $A \in M_\iota(K)$ such that
--   $$\mathrm{invFactors}(M) = \mathrm{invFactors}(M^{\mathsf{T}})$$
--   and for every $A$
--   $$\mathrm{sim}(A) \circ A \circ \mathrm{sim}(A)^{-1} = \mathrm{rcf}\bigl(\mathrm{invFactors}(\mathrm{charmatrix}\, A)\bigr).$$
--
--   This is the Smith normal form of matrices over the Euclidean domain $K[X]$, lifted from Mathlib's `Module.Basis.SmithNormalForm` / `Submodule.smithNormalForm` via `Polynomial.instEuclideanDomain`. It is the single poly-SNF child of `WeilConjectures.exists_invariant_factors_of_matrix`.
-- source:
--   Smith normal form over Euclidean domains; Mathlib Module.Basis.SmithNormalForm / Submodule.smithNormalForm; Polynomial.instEuclideanDomain; cf. Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- Smith normal form for square matrices over `Polynomial K` (`K` a field).

There exist:
* `invFactors` — the monic invariant-factor list of a matrix over `Polynomial K`;
* `rcf` — the companion-block matrix over `K` built from a factor list;
* `sim` — a similarity taking each `A : Matrix ι ι K` to `rcf` of the invariant
  factors of its characteristic matrix `charmatrix A`.

The factor list is transpose-invariant: `invFactors M = invFactors Mᵀ`
(SNF of `Mᵀ` coincides with that of `M` up to units, normalized monic).

**REUSE (A37 PID-LIFT):** lift Mathlib `Module.Basis.SmithNormalForm` /
`Submodule.smithNormalForm` along `Polynomial.instEuclideanDomain`
(`EuclideanDomain.to_principal_ideal_domain` on `Polynomial K`). Do not re-develop
the Euclidean row/column algorithm from scratch. -/

theorem WeilConjectures.exists_snf_of_polynomial_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (invFactors : Matrix ι ι (Polynomial K) → List (Polynomial K))
      (rcf : List (Polynomial K) → Matrix ι ι K)
      (sim : Matrix ι ι K → ((ι → K) ≃ₗ[K] (ι → K))),
      (∀ M, invFactors M = invFactors M.transpose) ∧
      (∀ A, (sim A).conj (Matrix.toLin' A) =
        Matrix.toLin' (rcf (invFactors (Matrix.charmatrix A)))) := by
  sorry
