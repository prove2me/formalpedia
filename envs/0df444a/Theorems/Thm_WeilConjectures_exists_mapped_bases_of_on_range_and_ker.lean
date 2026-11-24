-- Prove2me | Theorems.Thm_WeilConjectures_exists_mapped_bases_of_on_range_and_ker
-- name    : WeilConjectures.exists_mapped_bases_of_on_range_and_ker
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T03:43:10.472578+00:00
-- url     : https://prove2.me/theorems/6ec76675-1a52-464c-b5d0-0dc897a484e5
-- title:
--   Mapped Bases from On-Range Assignment and Free/Finite Kernel
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. Suppose that for every matrix $M \in M_\iota(K[X])$ one is given (i) an on-range mapped assignment: an embedding $e : \mathrm{Fin}\, n \hookrightarrow \iota$, a target basis $b_{\mathrm{tgt}}$, and vectors $v_j$ with
--   $$\mathrm{toLin}'(M)(v_j) = d(M)(e(j))\, b_{\mathrm{tgt}}(e(j)),$$
--   and $d(M)(i)=0$ off-range; and (ii) freeness and finiteness of $\ker(\mathrm{toLin}' M)$ over $K[X]$. Then there exist bases $b_{\mathrm{src}}, b_{\mathrm{tgt}}'$ of $K[X]^\iota$ such that for all $i$,
--   $$\mathrm{toLin}'(M)\bigl(b_{\mathrm{src}}(i)\bigr) = d(M)(i)\, b_{\mathrm{tgt}}'(i).$$
--
--   This is the A56 ker-extend glue assembling on-range preimages with a kernel basis (via Free/Finite $\Rightarrow$ chooseBasis).
-- source:
--   Basis.mk / LinearIndependent; Module.Free / Module.Finite ker over PID; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A56 KER-EXTEND glue: from an on-range mapped assignment
`(e, bTgt, v)` with `toLin' M (v j) = d M (e j) • bTgt (e j)` and
`d = 0` off-range, together with freeness/finiteness of `ker (toLin' M)`,
assemble full bases `bSrc`, `bTgt'` satisfying
`toLin' M (bSrc i) = d M i • bTgt' i` for all `i`.

**REUSE:** `Basis.mk`, `LinearIndependent`, `LinearMap.ker`, `Module.Free`,
`Module.Finite`. -/

theorem WeilConjectures.exists_mapped_bases_of_on_range_and_ker
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hon : ∀ (M : Matrix ι ι (Polynomial K)), ∃ (n : ℕ) (e : Fin n ↪ ι)
      (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, Matrix.toLin' M (v j) = d M (e j) • bTgt (e j)) ∧
        (∀ i, (∀ j : Fin n, e j ≠ i) → d M i = 0))
    (_hker : ∀ (M : Matrix ι ι (Polynomial K)),
      Module.Free (Polynomial K) (LinearMap.ker (Matrix.toLin' M)) ∧
        Module.Finite (Polynomial K) (LinearMap.ker (Matrix.toLin' M))) :
    ∀ (M : Matrix ι ι (Polynomial K)),
      ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  sorry
