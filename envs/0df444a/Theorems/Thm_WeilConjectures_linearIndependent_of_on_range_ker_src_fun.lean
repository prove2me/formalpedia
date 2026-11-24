-- Prove2me | Theorems.Thm_WeilConjectures_linearIndependent_of_on_range_ker_src_fun
-- name    : WeilConjectures.linearIndependent_of_on_range_ker_src_fun
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T04:56:59.898032+00:00
-- url     : https://prove2.me/theorems/b42eca3d-1dfa-4cf8-8663-f26c108a1713
-- title:
--   Linear Independence of On-Range/Ker Source Family
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Suppose $f : \iota \to K[X]^\iota$ agrees with on-range preimages $v_j$, lands in $\ker(\mathrm{toLin}' M)$ off-range, satisfies the mapped equations against $b_{\mathrm{tgt}}$, and is compatible with a finite kernel basis $b_{\mathrm{ker}}$. Then $f$ is linearly independent over $K[X]$ (A60a).
-- source:
--   LinearIndependent; LinearMap.ker; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A60a: a mapped source family agreeing with on-range `v` and landing in
`ker (toLin' M)` off-range is linearly independent (via ker basis `bKer`).

**REUSE:** `LinearIndependent`, `LinearMap.ker.subtype`. -/

theorem WeilConjectures.linearIndependent_of_on_range_ker_src_fun
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
    LinearIndependent (Polynomial K) f := by
  sorry
