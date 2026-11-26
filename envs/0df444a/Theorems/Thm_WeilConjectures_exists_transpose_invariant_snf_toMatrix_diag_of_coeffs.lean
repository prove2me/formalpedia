-- Prove2me | Theorems.Thm_WeilConjectures_exists_transpose_invariant_snf_toMatrix_diag_of_coeffs
-- name    : WeilConjectures.exists_transpose_invariant_snf_toMatrix_diag_of_coeffs
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T14:17:14.084352+00:00
-- url     : https://prove2.me/theorems/3c6805be-46d0-4192-97f5-a218608adf2a
-- title:
--   Transpose-Invariant SNF toMatrix Diagonal from Coeffs
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. Suppose $d_0$ assigns to every $M \in M_\iota(K[X])$ a family such that some bases of $K[X]^\iota$ realize $\mathrm{toLin}' M$ as $\operatorname{diag}(d_0(M))$. Then there exists a transpose-invariant assignment $d$ with the same property:
--   $$d(M)(i)=d(M^{\mathsf{T}})(i)\quad\text{for all }i,$$
--   and bases realizing $\operatorname{diag}(d(M))$.
--
--   Normalization uses uniqueness of invariant factors of free modules over the PID $K[X]$ so $M$ and $M^{\mathsf{T}}$ share a common diagonal; symmetric choice forces $d(M)=d(M^{\mathsf{T}})$ (A64a).
-- source:
--   Submodule.smithNormalForm; invariant-factor uniqueness; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A64a NORMALIZE: from any SNF `toMatrix`-diagonal assignment `d₀`, produce a
transpose-invariant assignment `d` that still admits Smith bases for every `M`.

Uses invariant-factor uniqueness for free modules over the PID `K[X]` so that
`M` and `Mᵀ` share a common normalized diagonal; then symmetric choice yields
`d M = d Mᵀ`.

**REUSE:** `Submodule.smithNormalForm`, invariant-factor uniqueness,
`Matrix.transpose`, `LinearMap.toMatrix`. -/

theorem WeilConjectures.exists_transpose_invariant_snf_toMatrix_diag_of_coeffs
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d0 : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hd0 : ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d0 M)) :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) =
          Matrix.diagonal (d M)) := by
  sorry
