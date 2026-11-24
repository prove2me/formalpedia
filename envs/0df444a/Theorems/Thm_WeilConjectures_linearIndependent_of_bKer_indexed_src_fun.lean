-- Prove2me | Theorems.Thm_WeilConjectures_linearIndependent_of_bKer_indexed_src_fun
-- name    : WeilConjectures.linearIndependent_of_bKer_indexed_src_fun
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:09:40.18372+00:00
-- url     : https://prove2.me/theorems/4db67a26-8183-47c6-8f31-0e3aa3e4971b
-- title:
--   LI of Source Family under Ker-Basis Off-Range Indexing
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Suppose $f$ agrees with on-range preimages $v_j$, satisfies the mapped equations against $b_{\mathrm{tgt}}$, and off-range is indexed by a ker basis via an equivalence $\sigma$. Then $f$ is linearly independent over $K[X]$ (A60a').
-- source:
--   LinearIndependent; Basis.linearIndependent; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A60a': under an off-range `bKer`-indexing equiv `σ`, a mapped source family
agreeing with on-range `v` is linearly independent.

**REUSE:** `LinearIndependent`, `Basis.linearIndependent`. -/

theorem WeilConjectures.linearIndependent_of_bKer_indexed_src_fun
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
    (σ : {i : ι // ∀ j : Fin n, e j ≠ i} ≃ Fin m)
    (hσ : ∀ i (h : ∀ j : Fin n, e j ≠ i),
      f i = (bKer (σ ⟨i, h⟩) : ι → Polynomial K)) :
    LinearIndependent (Polynomial K) f := by
  sorry
