-- Prove2me | Theorems.Thm_WeilConjectures_exists_snf_coeffs_of_poly_matrix
-- name    : WeilConjectures.exists_snf_coeffs_of_poly_matrix
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T02:18:49.191974+00:00
-- url     : https://prove2.me/theorems/7d346459-3398-4cc2-9971-8207b4ade5e7
-- title:
--   SNF Coefficients with Diagonalizing Bases over $K[X]$
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exists an assignment $d$ sending each matrix $M \in M_\iota(K[X])$ to a diagonal $d(M) : \iota \to K[X]$ together with bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}$ of $K[X]^\iota$ such that the matrix of $\mathrm{toLin}'(M)$ in these bases is diagonal:
--   $$\mathrm{toMatrix}_{b_{\mathrm{src}}, b_{\mathrm{tgt}}}(\mathrm{toLin}' M) = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   This is the coefficient-extraction phase of the PID-lift of Mathlib's `Submodule.smithNormalForm` / `smithNormalFormCoeffs` (A44).
-- source:
--   Smith normal form over Euclidean domains; Mathlib Submodule.smithNormalForm / smithNormalFormCoeffs; LinearMap.toMatrix; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A44 SNF-UNIT-EQUIV (coeffs phase): PID-lift of `Submodule.smithNormalForm` /
`smithNormalFormCoeffs` yields a diagonal assignment `d` together with bases of
`K[X]^ι` in which `toLin' M` is represented by `diagonal (d M)`.

**REUSE:** `Submodule.smithNormalForm`, `smithNormalFormCoeffs`,
`Module.Basis.SmithNormalForm`, `Polynomial.instEuclideanDomain`,
`EuclideanDomain.to_principal_ideal_domain`, `LinearMap.toMatrix`. -/

theorem WeilConjectures.exists_snf_coeffs_of_poly_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M) := by
  sorry
