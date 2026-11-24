-- Prove2me | Theorems.Thm_WeilConjectures_exists_mapped_bases_of_snf_preimage_family
-- name    : WeilConjectures.exists_mapped_bases_of_snf_preimage_family
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T03:31:51.774839+00:00
-- url     : https://prove2.me/theorems/eb4eedb7-41b9-43b5-87ff-e35112c37877
-- title:
--   Mapped Bases from SNF Preimage Family and Kernel Extension
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $d$ a diagonal assignment equipped, for every $M \in M_\iota(K[X])$, with a Smith witness $(n,\mathrm{snf})$ and on-range preimages $v_j$ satisfying
--   $$\mathrm{toLin}'(M)(v_j) = d(M)(f(j))\, b_M(f(j)).$$
--   Then there exist bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}$ of $K[X]^\iota$ such that for all $i$,
--   $$\mathrm{toLin}'(M)\bigl(b_{\mathrm{src}}(i)\bigr) = d(M)(i)\, b_{\mathrm{tgt}}(i).$$
--
--   Extend the preimage family by a kernel basis off-range (A54).
-- source:
--   Module.Basis.SmithNormalForm; Basis.mk / LinearIndependent; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A54 ker-extend / full mapped-bases assembly: given SNF witnesses plus on-range
preimages `v j` with `toLin' M (v j) = d M (f j) • bM (f j)`, extend by a kernel
basis off-range to full bases `bSrc`, `bTgt` satisfying
`toLin' M (bSrc i) = d M i • bTgt i` for all `i`.

**REUSE:** `Module.Basis.SmithNormalForm`, `Basis.mk`, `LinearIndependent`,
`LinearMap.ker`, `Pi.basisFun`. -/

theorem WeilConjectures.exists_mapped_bases_of_snf_preimage_family
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpre : ∀ M, ∃ (n : ℕ)
      (snf : Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' M)) ι n)
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, d M (snf.f j) = snf.a j) ∧
      (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) ∧
      (∀ j, Matrix.toLin' M (v j) = d M (snf.f j) • snf.bM (snf.f j))) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  sorry
