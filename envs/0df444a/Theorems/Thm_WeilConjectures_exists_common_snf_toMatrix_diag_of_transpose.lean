-- Prove2me | Theorems.Thm_WeilConjectures_exists_common_snf_toMatrix_diag_of_transpose
-- name    : WeilConjectures.exists_common_snf_toMatrix_diag_of_transpose
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T16:57:08.348997+00:00
-- url     : https://prove2.me/theorems/54ee060f-edeb-4d73-a119-9417f4210897
-- title:
--   Common SNF toMatrix Diagonal for Matrix and Transpose
-- statement:
--   Let $K$ be a field and $\iota$ a finite index type. Suppose $d_0$ is any assignment such that every $M\in M_\iota(K[X])$ admits bases realizing $\mathrm{toLin}'M$ as $\operatorname{diag}(d_0(M))$. Then for every $M$ there exists a single family $a:\iota\to K[X]$ that is realized as a $\mathrm{toMatrix}$-diagonal for both $M$ and $M^{\mathsf{T}}$.
--
--   This is the common invariant-factor diagonal for a matrix and its transpose over the PID $K[X]$ (A64b).
-- source:
--   Submodule.smithNormalForm; invariant-factor uniqueness; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A64b COMMON-DIAG: for every matrix `M` over `K[X]`, there is a single diagonal
family `a` realized as `toMatrix` for both `M` and `Mᵀ` (same invariant factors).

**REUSE:** `Submodule.smithNormalForm`, invariant-factor uniqueness,
`Matrix.transpose`, `LinearMap.toMatrix`. -/

theorem WeilConjectures.exists_common_snf_toMatrix_diag_of_transpose
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d0 : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hd0 : ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d0 M)) :
    ∀ M : Matrix ι ι (Polynomial K),
      ∃ (a : ι → Polynomial K),
        (∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
          LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal a) ∧
        (∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
          LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M.transpose) =
            Matrix.diagonal a) := by
  sorry
