-- Prove2me | Theorems.Thm_WeilConjectures_span_top_of_on_range_ker_src_fun
-- name    : WeilConjectures.span_top_of_on_range_ker_src_fun
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T04:57:01.196781+00:00
-- url     : https://prove2.me/theorems/bb204375-5684-4bc0-9a25-8f50870f088d
-- title:
--   Top Span of On-Range/Ker Source Family
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Suppose $f : \iota \to K[X]^\iota$ agrees with on-range preimages $v_j$, lands in $\ker(\mathrm{toLin}' M)$ off-range, satisfies the mapped equations against $b_{\mathrm{tgt}}$, and is compatible with a finite kernel basis $b_{\mathrm{ker}}$. Then
--   $$\top \le \operatorname{span}_{K[X]}(\operatorname{range} f),$$
--   i.e. $f$ spans the ambient module (A60b).
-- source:
--   Submodule.span; Fintype.card; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A60b: a mapped source family agreeing with on-range `v` and landing in
`ker (toLin' M)` off-range spans the ambient module (via ker basis `bKer`).

**REUSE:** `Submodule.span`, `Fintype.card`, `Basis.repr`. -/

theorem WeilConjectures.span_top_of_on_range_ker_src_fun
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M)))
    (f : ι → (ι → Polynomial K))
    (hmap : ∀ i, Matrix.toLin' M (f i) = d i • bTgt i)
    (hon : ∀ j, f (e j) = v j)
    (hker : ∀ i, (∀ j : Fin n, e j ≠ i) →
      f i ∈ LinearMap.ker (Matrix.toLin' M)) :
    ⊤ ≤ Submodule.span (Polynomial K) (Set.range f) := by
  sorry
