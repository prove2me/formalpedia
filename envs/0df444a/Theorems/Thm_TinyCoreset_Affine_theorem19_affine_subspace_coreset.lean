-- Prove2me | Theorems.Thm_TinyCoreset_Affine_theorem19_affine_subspace_coreset
-- name    : TinyCoreset.Affine.theorem19_affine_subspace_coreset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:12.659267+00:00
-- url     : https://prove2.me/theorems/d498f3fe-b6b3-4438-b32b-d1d6e593c201
-- title:
--   Theorem 19, p. 617 — Algorithm 2's 2m weighted points plus Δ form a (1 + ε) coreset for affine j-subspaces
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ with $n\ge1$, let $j\in[1,d-1]$ be an integer and let $\varepsilon>0$. Run Algorithm 2 (affine-$j$-subspace-Coreset$(A,j,\varepsilon)$):
--
--   1. compute the mean row $\mu(A)=\frac1n\sum_{i=1}^nA_{i*}$ and the centred matrix $A'=A-\mathbb 1\cdot\mu(A)$;
--   2. fix any singular value decomposition $A'=U\Sigma V^T$ and run Algorithm 1 on $A'$, obtaining $m=\min\{n,d,j+\lceil j/\varepsilon\rceil-1\}$, the matrix $S'$ of the first $m$ rows of $\Sigma^{(m)}V^T$, and $\Delta=\|A'-A'^{(m)}\|_F^2$;
--   3. output $S=\mathbb 1\cdot\mu(A)+\sqrt{m/n}\cdot\begin{bmatrix}S'\\-S'\end{bmatrix}$ and the weights $w_1=\cdots=w_{2m}=n/(2m)$.
--
--   Then $S\in\mathbb R^{(2m)\times d}$, $m\le j+\lceil j/\varepsilon\rceil-1$, $\Delta\ge0$, and for every affine $j$-dimensional subspace $C$ of $\mathbb R^d$,
--
--   $$\operatorname{dist}^2(A,C)\le\sum_{i=1}^{2m}w_i\cdot\operatorname{dist}^2(S_{i*},C)+\Delta\le(1+\varepsilon)\cdot\operatorname{dist}^2(A,C).$$
--
--   This is a coreset for PCA on data that is not centred: $2m=O(j/\varepsilon)$ weighted points and one constant, independent of $n$ and $d$, approximate the cost of every affine $j$-subspace simultaneously.
--
--   **Formalization Note** The paper states "$\Delta>0$", which is false when all points coincide ($A'=0$) or more generally when $\operatorname{rank}A'\le m$; the statement claims $\Delta\ge0$. The call "affine-$j$-subspace-Coreset$(P,j,\varepsilon)$" is read with $P=A$. $n\ge1$ is added because Algorithm 2 divides by $n$. An affine $j$-subspace is an `AffineSubspace` whose direction has dimension $j$; the hypothesis that it is nonempty is implied by $j\ge1$ and is kept as a guard for Mathlib's convention that the distance to the empty set is $0$. The output type `Fin (m + m)` encodes $S\in\mathbb R^{(2m)\times d}$. The SVD of $A'$ is arbitrary. The running-time clause is not formalized.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 617, Theorem 19 and Algorithm 2 (p. 616); proof pp. 617–618

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_Affine_Setting

namespace TinyCoreset.Affine

open scoped Matrix

/-- Theorem 19, p. 617 (coreset for affine j-subspace). Run Algorithm 2
(`affine-j-subspace-Coreset(A, j, ε)`): centre `A` at its mean row `µ(A)`, take an arbitrary SVD
`A′ = U S Vᵀ` of the centred matrix `A′ = A − 𝟙 · µ(A)`, run Algorithm 1 on `A′` to get `m`, `S′`
(first `m` rows of `Σ^(m) Vᵀ`) and `Δ = ‖A′ − A′^(m)‖²_F`, and output the `2m` points
`µ(A) ± √(m/n) · S′_{i*}`, each with weight `n/(2m)`. Then the output has `2m` rows,
`m ≤ j + ⌈j/ε⌉ − 1`, `Δ ≥ 0` (the page's "Δ > 0" is false when all points coincide), and for every
affine `j`-dimensional subspace `C` of `ℝ^d`,
`dist²(A, C) ≤ Σ_{i=1}^{2m} w_i dist²(S_{i*}, C) + Δ ≤ (1 + ε) · dist²(A, C)`. -/
theorem theorem19_affine_subspace_coreset {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
    (hA : ProjLikeRetr.FixedRank.IsSVD (center A) U S V) (hn : 1 ≤ n)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    coresetSize n d j ε + 1 ≤ j + ⌈(j : ℝ) / ε⌉₊ ∧
    0 ≤ TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
    ∀ C : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ C.direction = j →
      (C : Set (EuclideanSpace ℝ (Fin d))).Nonempty →
      TinyCoreset.DimRed.distSq A (C : Set (EuclideanSpace ℝ (Fin d))) ≤
          TinyCoreset.DimRed.wDistSq (fun _ => affineWeight n (coresetSize n d j ε))
              (affineCoresetRows n (mean A)
                (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
              (C : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
        TinyCoreset.DimRed.wDistSq (fun _ => affineWeight n (coresetSize n d j ε))
              (affineCoresetRows n (mean A)
                (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
              (C : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ≤
          (1 + ε) * TinyCoreset.DimRed.distSq A (C : Set (EuclideanSpace ℝ (Fin d))) := by sorry

end TinyCoreset.Affine
