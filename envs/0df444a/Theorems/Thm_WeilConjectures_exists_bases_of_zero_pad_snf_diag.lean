-- Prove2me | Theorems.Thm_WeilConjectures_exists_bases_of_zero_pad_snf_diag
-- name    : WeilConjectures.exists_bases_of_zero_pad_snf_diag
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T02:51:47.85325+00:00
-- url     : https://prove2.me/theorems/1e5e67c3-576c-4a39-b7b9-b070da070b07
-- title:
--   Diagonalizing Bases from Zero-Padded SNF Diagonal
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ a zero-padded SNF diagonal assignment with Smith witnesses as in `exists_zero_pad_diag_of_range_snf`. Then for every $M$ there exist bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}$ of $K[X]^\iota$ such that
--   $$\mathrm{toMatrix}_{b_{\mathrm{src}}, b_{\mathrm{tgt}}}(\mathrm{toLin}' M) = \operatorname{diag}\bigl(d(M)\bigr).$$
--
--   Reindex / extend `snf.bM` via `Basis.reindex` and the standard `Pi.basisFun` (A49) — no ad-hoc entry formulas.
-- source:
--   LinearMap.toMatrix; Basis.reindex; Pi.basisFun; Module.Basis.SmithNormalForm

import Mathlib

/-- A49 REINDEX-PAD: given a zero-padded SNF diagonal `d` with Smith witnesses,
produce full-ι bases `bSrc`, `bTgt` such that
`toMatrix bSrc bTgt (toLin' M) = diagonal (d M)`.

Prefer `Basis.reindex` / `snf.bM` and `Pi.basisFun` — no ad-hoc entry formulas.

**REUSE:** `Module.Basis.SmithNormalForm`, `LinearMap.toMatrix`, `Pi.basisFun`,
`Basis.reindex`, `Matrix.toLin'`. -/

theorem WeilConjectures.exists_bases_of_zero_pad_snf_diag
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpad : ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0)) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M) := by
  sorry
