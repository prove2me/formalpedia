-- Prove2me | Theorems.Thm_WeilConjectures_exists_mapped_bases_of_zero_pad_snf_diag
-- name    : WeilConjectures.exists_mapped_bases_of_zero_pad_snf_diag
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T03:24:34.018689+00:00
-- url     : https://prove2.me/theorems/da358f21-bd6e-49b8-9706-6b09439e058b
-- title:
--   Mapped Bases from Zero-Padded SNF Diagonal
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ a zero-padded SNF diagonal assignment with Smith witnesses. Then for every matrix $M \in M_\iota(K[X])$ there exist bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}$ of $K[X]^\iota$ such that for all indices $i$,
--   $$\mathrm{toLin}'(M)\bigl(b_{\mathrm{src}}(i)\bigr) = d(M)(i)\, b_{\mathrm{tgt}}(i).$$
--
--   This is the mapped-bases form of Smith diagonalization used to deduce `toMatrix = diag(d(M))` (A53).
-- source:
--   Module.Basis.SmithNormalForm; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A53 TOMATRIX-OF-SNF (mapped-bases phase): from a zero-padded SNF diagonal `d`
with Smith witnesses, produce bases `bSrc`, `bTgt` of `K[X]^ι` satisfying
`toLin' M (bSrc i) = d M i • bTgt i` for all `i`.

**REUSE:** `Module.Basis.SmithNormalForm`, `Pi.basisFun`, `Basis.reindex`,
`Matrix.toLin'`. -/

theorem WeilConjectures.exists_mapped_bases_of_zero_pad_snf_diag
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpad : ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0)) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  sorry
