-- Prove2me | Theorems.Thm_WeilConjectures_exists_zero_pad_diag_of_range_snf
-- name    : WeilConjectures.exists_zero_pad_diag_of_range_snf
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T02:51:46.130176+00:00
-- url     : https://prove2.me/theorems/e8c55f2d-80e4-4b27-a3e5-28de1034ba28
-- title:
--   Zero-Padded SNF Diagonal from Range Smith Form
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. Assume every matrix $M \in M_\iota(K[X])$ has a Smith normal form on $\operatorname{im}(\mathrm{toLin}' M)$. Then there exists a full-index diagonal assignment $d$ such that for each $M$ there is a Smith witness $(n, \mathrm{snf})$ with
--   $$d(M)(f(j)) = a(j) \quad\text{and}\quad d(M)(i) = 0 \text{ for } i \notin \operatorname{range}(f),$$
--   where $f : \mathrm{Fin}\, n \hookrightarrow \iota$ and $a$ are the Smith embedding and coefficients.
--
--   This is the zero-pad extraction of invariant factors onto $\iota$ (A50).
-- source:
--   Module.Basis.SmithNormalForm; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A50 ZERO-PAD-EMBED: from range-SNF data, extract a full-ι diagonal `d`
with `d (f j) = a j` on the Smith embedding and `d i = 0` off-range.

**REUSE:** `Module.Basis.SmithNormalForm`, `Function.Embedding`. -/

theorem WeilConjectures.exists_zero_pad_diag_of_range_snf
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (hSNF : ∀ M : Matrix ι ι (Polynomial K),
      ∃ (n : ℕ),
        Nonempty
          (Module.Basis.SmithNormalForm
            (LinearMap.range (Matrix.toLin' M)) ι n)) :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) := by
  sorry
