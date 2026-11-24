-- Prove2me | Theorems.Thm_WeilConjectures_exists_mapped_bases_of_on_range_src_and_ker_basis
-- name    : WeilConjectures.exists_mapped_bases_of_on_range_src_and_ker_basis
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T03:57:41.582907+00:00
-- url     : https://prove2.me/theorems/4bf54c94-722d-444f-b3b8-aa1e13b92c8d
-- title:
--   Mapped Source Basis from On-Range Vectors and Kernel Basis
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Given an on-range assignment — embedding $e : \mathrm{Fin}\, n \hookrightarrow \iota$, target basis $b_{\mathrm{tgt}}$, and vectors $v_j$ with
--   $$\mathrm{toLin}'(M)(v_j) = d(e(j))\, b_{\mathrm{tgt}}(e(j)),$$
--   and $d(i)=0$ off-range — together with a finite kernel basis $b_{\mathrm{ker}} : \mathrm{Fin}\, m \to \ker(\mathrm{toLin}' M)$, there exists a source basis $b_{\mathrm{src}}$ of $K[X]^\iota$ such that for all $i$,
--   $$\mathrm{toLin}'(M)\bigl(b_{\mathrm{src}}(i)\bigr) = d(i)\, b_{\mathrm{tgt}}(i).$$
--
--   Assemble via Basis.mk / LinearIndependent (A57), using on-range $v$ and off-range ker vectors.
-- source:
--   Basis.mk / LinearIndependent; Free.chooseBasis; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A57 BASIS-MK-LI: from a concrete on-range assignment `(e, bTgt, v)` and a
finite kernel basis `bKer`, assemble a source basis `bSrc` with
`toLin' M (bSrc i) = d i • bTgt i` for all `i`
(on-range via `v`, off-range via ker vectors / `Basis.mk`).

**REUSE:** `Basis.mk`, `LinearIndependent`, `Module.Free.chooseBasis`. -/

theorem WeilConjectures.exists_mapped_bases_of_on_range_src_and_ker_basis
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    (hv : ∀ j, Matrix.toLin' M (v j) = d (e j) • bTgt (e j))
    (hoff : ∀ i, (∀ j : Fin n, e j ≠ i) → d i = 0)
    {m : ℕ}
    (_bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M))) :
    ∃ (bSrc : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d i • bTgt i := by
  sorry
