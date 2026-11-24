-- Prove2me | Theorems.Thm_WeilConjectures_exists_on_range_bSrc_assign
-- name    : WeilConjectures.exists_on_range_bSrc_assign
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T04:12:05.153035+00:00
-- url     : https://prove2.me/theorems/0eda09e2-d599-4dda-ae03-e8df9f619702
-- title:
--   On-Range Source Assign from Preimages and Kernel Basis
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Given an on-range assignment $(e, b_{\mathrm{tgt}}, v)$ with
--   $$\mathrm{toLin}'(M)(v_j) = d(e(j))\, b_{\mathrm{tgt}}(e(j)),$$
--   and $d=0$ off-range, together with a finite kernel basis $b_{\mathrm{ker}}$, there exists a family $f : \iota \to K[X]^\iota$ such that $f(e(j))=v_j$, off-range values lie in $\ker(\mathrm{toLin}' M)$, and
--   $$\mathrm{toLin}'(M)(f(i)) = d(i)\, b_{\mathrm{tgt}}(i)$$
--   for all $i$ (A59: dite on-range / ker off-range assign).
-- source:
--   dite; Classical.choose; LinearMap.ker.subtype; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A59 DITE-ON-RANGE: build `f : ι → K[X]^ι` from on-range `v` and ker basis
`bKer` so that `f (e j) = v j`, off-range values lie in `ker (toLin' M)`, and
`toLin' M (f i) = d i • bTgt i` for all `i`.

**REUSE:** `dite`, `Classical.choose`, `LinearMap.ker.subtype`. -/

theorem WeilConjectures.exists_on_range_bSrc_assign
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    (hv : ∀ j, Matrix.toLin' M (v j) = d (e j) • bTgt (e j))
    (hoff : ∀ i, (∀ j : Fin n, e j ≠ i) → d i = 0)
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M))) :
    ∃ (f : ι → (ι → Polynomial K)),
      (∀ i, Matrix.toLin' M (f i) = d i • bTgt i) ∧
        (∀ j, f (e j) = v j) ∧
          (∀ i, (∀ j : Fin n, e j ≠ i) →
            f i ∈ LinearMap.ker (Matrix.toLin' M)) := by
  sorry
