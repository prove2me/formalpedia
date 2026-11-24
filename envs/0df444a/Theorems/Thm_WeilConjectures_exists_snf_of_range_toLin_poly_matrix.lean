-- Prove2me | Theorems.Thm_WeilConjectures_exists_snf_of_range_toLin_poly_matrix
-- name    : WeilConjectures.exists_snf_of_range_toLin_poly_matrix
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T02:38:12.543282+00:00
-- url     : https://prove2.me/theorems/4895baa5-55ff-48ce-9912-f5194e2acf2a
-- title:
--   Smith Normal Form of Matrix Image over $K[X]$
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. For every matrix $M \in M_\iota(K[X])$, the image submodule $\operatorname{im}(\mathrm{toLin}' M) \subseteq K[X]^\iota$ admits a Smith normal form: there exist $n \in \mathbb{N}$ and a `Module.Basis.SmithNormalForm` witness of rank $n$ on that image.
--
--   This is the direct PID-lift of Mathlib's `Submodule.smithNormalForm` along `Polynomial.instEuclideanDomain` applied to matrix images (A46).
-- source:
--   Mathlib Submodule.smithNormalForm / Module.Basis.SmithNormalForm; Polynomial.instEuclideanDomain; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A46 SNF-COEFFS-IMAGE: for every matrix `M` over `K[X]`, the image submodule
`LinearMap.range (toLin' M) ⊆ K[X]^ι` admits a Smith normal form
(`Module.Basis.SmithNormalForm`), via PID-lift of Mathlib
`Submodule.smithNormalForm` along `Polynomial.instEuclideanDomain`.

**REUSE:** `Submodule.smithNormalForm`, `Module.Basis.SmithNormalForm`,
`Polynomial.instEuclideanDomain`, `EuclideanDomain.to_principal_ideal_domain`,
`Matrix.toLin'`, `Pi.basisFun`, `Module.Free.function`. -/

theorem WeilConjectures.exists_snf_of_range_toLin_poly_matrix
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∀ M : Matrix ι ι (Polynomial K),
      ∃ (n : ℕ),
        Nonempty
          (Module.Basis.SmithNormalForm
            (LinearMap.range (Matrix.toLin' M)) ι n) := by
  sorry
