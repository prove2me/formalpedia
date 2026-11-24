-- Prove2me | Theorems.Thm_WeilConjectures_exists_diag_bases_of_range_snf
-- name    : WeilConjectures.exists_diag_bases_of_range_snf
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:38:13.187809+00:00
-- url     : https://prove2.me/theorems/75ba6e1c-a0d2-452e-b88a-2ae161919071
-- title:
--   Full-Index Diagonal Bases from Range Smith Form
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. Assume that for every $M \in M_\iota(K[X])$ the image $\operatorname{im}(\mathrm{toLin}' M)$ admits a Smith normal form. Then there exists a diagonal assignment $d : M_\iota(K[X]) \to (\iota \to K[X])$ and, for each $M$, bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}$ of $K[X]^\iota$ such that
--   $$\mathrm{toMatrix}_{b_{\mathrm{src}}, b_{\mathrm{tgt}}}(\mathrm{toLin}' M) = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   This reindexes / zero-pads deficient-rank Smith data onto the full index type $\iota$ (A47), producing the coefficient package consumed by `WeilConjectures.exists_snf_coeffs_of_poly_matrix`.
-- source:
--   Module.Basis.SmithNormalForm reindexing; LinearMap.toMatrix; Pi.basisFun; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A47 reindex-to-full-ι: from range-SNF existence, assemble a global diagonal
assignment `d` and full-index bases `bSrc`, `bTgt` of `K[X]^ι` such that
`toMatrix bSrc bTgt (toLin' M) = diagonal (d M)`.

Pads deficient-rank Smith data with zeros / extends the embedding `f : Fin n ↪ ι`
to a full reindexing; uses `Module.Basis` (A47) and `Pi.basisFun` as the standard
reference — no ad-hoc entry formulas.

**REUSE:** `Module.Basis.SmithNormalForm`, `LinearMap.toMatrix`, `Pi.basisFun`,
`Basis.reindex`. -/

theorem WeilConjectures.exists_diag_bases_of_range_snf
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (hSNF : ∀ M : Matrix ι ι (Polynomial K),
      ∃ (n : ℕ),
        Nonempty
          (Module.Basis.SmithNormalForm
            (LinearMap.range (Matrix.toLin' M)) ι n)) :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M) := by
  sorry
