-- Prove2me | Theorems.Thm_WeilConjectures_exists_normalized_snf_toMatrix_diag_transpose_invariant
-- name    : WeilConjectures.exists_normalized_snf_toMatrix_diag_transpose_invariant
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T05:16:13.992989+00:00
-- url     : https://prove2.me/theorems/612d4b3a-f7f7-46a7-9850-e045e090aa72
-- title:
--   Normalized Transpose-Invariant SNF toMatrix Diagonal
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. There exists a normalized Smith diagonal assignment $d$ such that for every $M \in M_\iota(K[X])$,
--   $$d(M)(i) = d(M^{\mathsf{T}})(i) \quad\text{for all } i,$$
--   and there are bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}$ of $K[X]^\iota$ with
--   $$\mathrm{toMatrix}_{b_{\mathrm{src}},b_{\mathrm{tgt}}}(\mathrm{toLin}' M) = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   Normalization (invariant-factor uniqueness) ensures transpose invariance; this replaces the Disproved claim that every unit-fac diagonal is transpose-invariant (A64).
-- source:
--   Submodule.smithNormalForm; invariant-factor uniqueness; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A64 DIAG-UNIQUE / A63': there exists a normalized SNF diagonal assignment
`d` with `toMatrix bSrc bTgt (toLin' M) = diagonal (d M)` for every `M`, and
with `d M = d Mᵀ` pointwise (invariant factors of `M` and `Mᵀ` agree).

**REUSE:** `Submodule.smithNormalForm`, uniqueness of invariant factors,
`Matrix.transpose`, `LinearMap.toMatrix`. -/

theorem WeilConjectures.exists_normalized_snf_toMatrix_diag_transpose_invariant
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) =
          Matrix.diagonal (d M)) := by
  sorry
