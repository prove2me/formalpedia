-- Prove2me | Theorems.Thm_WeilConjectures_exists_li_mapped_src_fun_of_on_range_and_ker_basis
-- name    : WeilConjectures.exists_li_mapped_src_fun_of_on_range_and_ker_basis
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T04:04:46.053058+00:00
-- url     : https://prove2.me/theorems/ed152c69-5eac-4dd3-b263-2bceb5327fb7
-- title:
--   LI Mapped Source Family from On-Range and Kernel Basis
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Given an on-range assignment $(e, b_{\mathrm{tgt}}, v)$ with
--   $$\mathrm{toLin}'(M)(v_j) = d(e(j))\, b_{\mathrm{tgt}}(e(j)),$$
--   and $d=0$ off-range, together with a finite kernel basis $b_{\mathrm{ker}}$, there exists a family $f : \iota \to K[X]^\iota$ that is linearly independent, spans the ambient module, and satisfies
--   $$\mathrm{toLin}'(M)(f(i)) = d(i)\, b_{\mathrm{tgt}}(i)$$
--   for all $i$ (A57/A59: on-range via $v$, off-range via ker).
-- source:
--   LinearIndependent; Submodule.span; dite on-range; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A57/A59: from on-range `(e, v)` and ker basis `bKer`, produce a family
`f : ι → K[X]^ι` that is linearly independent, spans the top submodule, and
satisfies `toLin' M (f i) = d i • bTgt i` for all `i`
(on-range via `v`, off-range via ker vectors).

**REUSE:** `dite`, `LinearIndependent`, `Submodule.span`, `LinearMap.ker.subtype`. -/

theorem WeilConjectures.exists_li_mapped_src_fun_of_on_range_and_ker_basis
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
        LinearIndependent (Polynomial K) f ∧
          ⊤ ≤ Submodule.span (Polynomial K) (Set.range f) := by
  sorry
