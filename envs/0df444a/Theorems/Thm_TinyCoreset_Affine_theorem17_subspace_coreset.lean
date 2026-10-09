-- Prove2me | Theorems.Thm_TinyCoreset_Affine_theorem17_subspace_coreset
-- name    : TinyCoreset.Affine.theorem17_subspace_coreset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:13.179988+00:00
-- url     : https://prove2.me/theorems/87cf9acb-27b5-44d9-8ee4-17d186e78499
-- title:
--   Theorem 17, p. 615 — the first m rows of Σ^(m)Vᵀ plus Δ form a (1 + ε) coreset for linear j-subspaces
-- statement:
--   Let $A\in\mathbb R^{n\times d}$, let $j\ge1$ be an integer and let $\varepsilon>0$. Fix any singular value decomposition $A=U\Sigma V^T$ and run Algorithm 1: let $m=\min\{n,d,j+\lceil j/\varepsilon\rceil-1\}$, let $S\in\mathbb R^{m\times d}$ consist of the first $m$ rows of $\Sigma^{(m)}V^T$, let all weights be $w_i=1$, and let $\Delta=\|A-A^{(m)}\|_F^2$. Then $m\le j+\lceil j/\varepsilon\rceil-1$, $\Delta\ge0$, and for every $j$-dimensional linear subspace $L$ of $\mathbb R^d$,
--
--   $$\operatorname{dist}^2(A,L)\le\sum_{i=1}^m w_i\cdot\operatorname{dist}^2(S_{i*},L)+\Delta\le(1+\varepsilon)\cdot\operatorname{dist}^2(A,L).$$
--
--   So $m=O(j/\varepsilon)$ points, independent of $n$ and $d$, together with one constant, approximate the cost of every linear $j$-subspace. It is the building block of the affine coreset of Theorem 19.
--
--   **Formalization Note** The paper states "$\Delta>0$", which is false whenever $\operatorname{rank}A\le m$ (for instance $A=0$ or $m=\min\{n,d\}$); the statement claims $\Delta\ge0$. The paper's "$S\in\mathbb R^{m\times d}$" is realized by taking the first $m$ rows of $\Sigma^{(m)}V^T$, as the text before the theorem says (Algorithm 1, line 3 writes the whole $n\times d$ matrix, whose other rows are zero). The call "subspace-Coreset$(P,j,\varepsilon)$" is read with $P=A$. The SVD is arbitrary: the claim is made for every singular value decomposition of $A$. $m\le j+\lceil j/\varepsilon\rceil-1$ is written $m+1\le j+\lceil j/\varepsilon\rceil$. The running-time clause is not formalized.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 615, Theorem 17 and Algorithm 1

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_Affine_Setting

namespace TinyCoreset.Affine

open scoped Matrix

/-- Theorem 17, p. 615 (coreset for j-subspace). Run Algorithm 1 (`subspace-Coreset(A, j, ε)`) on
`A` with an arbitrary SVD `A = U S Vᵀ`: `m = min{n, d, j + ⌈j/ε⌉ − 1}`, the coreset `S′` is the first
`m` rows of `Σ^(m) Vᵀ` with all weights `1`, and `Δ = ‖A − A^(m)‖²_F`. Then `m ≤ j + ⌈j/ε⌉ − 1`,
`Δ ≥ 0` (the page's "Δ > 0" is false when `rank A ≤ m`), and for every `j`-dimensional linear
subspace `L`, `dist²(A, L) ≤ Σ_i w_i dist²(S′_{i*}, L) + Δ ≤ (1 + ε) dist²(A, L)`. -/
theorem theorem17_subspace_coreset {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
    (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (ε : ℝ) (hε : 0 < ε) :
    coresetSize n d j ε + 1 ≤ j + ⌈(j : ℝ) / ε⌉₊ ∧
    0 ≤ TinyCoreset.DimRed.frobSq (A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
    ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ L = j →
      TinyCoreset.DimRed.distSq A (L : Set (EuclideanSpace ℝ (Fin d))) ≤
          TinyCoreset.DimRed.wDistSq (fun _ => (1 : ℝ))
              (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V)
              (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
        TinyCoreset.DimRed.wDistSq (fun _ => (1 : ℝ))
              (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V)
              (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ≤
          (1 + ε) * TinyCoreset.DimRed.distSq A (L : Set (EuclideanSpace ℝ (Fin d))) := by sorry

end TinyCoreset.Affine
