-- Prove2me | Theorems.Thm_TinyCoreset_Affine_eq7_symmetrized_coreset
-- name    : TinyCoreset.Affine.eq7_symmetrized_coreset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:03.815596+00:00
-- url     : https://prove2.me/theorems/1a78d709-e2cd-4f8c-adb4-93ea6601f9f3
-- title:
--   (7), proof of Theorem 19, p. 618 — S″ = √(m/n)[S′; −S′] with weight n/(2m) is a coreset for A′ and linear j-subspaces
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ with $n\ge1$, let $j\in[1,d-1]$ be an integer and $\varepsilon>0$. Let $A'=A-\mathbb 1\cdot\mu(A)$ be the translation of $A$ by $-\mu(A)$, fix any singular value decomposition $A'=U\Sigma V^T$, and run Algorithm 1 on $A'$: $m=\min\{n,d,j+\lceil j/\varepsilon\rceil-1\}$, $S'$ the first $m$ rows of $\Sigma^{(m)}V^T$, $\Delta=\|A'-A'^{(m)}\|_F^2$. Set $S''=\sqrt{m/n}\cdot\begin{bmatrix}S'\\-S'\end{bmatrix}\in\mathbb R^{2m\times d}$. Then for every $j$-dimensional linear subspace $L$ of $\mathbb R^d$,
--
--   $$\operatorname{dist}^2(A',L)\le\frac{n}{2m}\cdot\operatorname{dist}^2(S'',L)+\Delta\le(1+\varepsilon)\cdot\operatorname{dist}^2(A',L).\tag{7}$$
--
--   The symmetrized, rescaled set $S''$ has mean $\vec 0$ and the same weighted cost as $S'$ on linear subspaces, so it can be combined with Lemma 18 to handle affine subspaces.
--
--   **Formalization Note** $n\ge1$ is added because Algorithm 2 divides by $n$. The SVD of $A'$ is arbitrary. The rows of $S''$ are ordered $\sqrt{m/n}\,S'_{i*}$ ($i=1,\ldots,m$) followed by $-\sqrt{m/n}\,S'_{i*}$.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 618, display (7) in the proof of Theorem 19

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_Affine_Setting

namespace TinyCoreset.Affine

open scoped Matrix

/-- Display (7), proof of Theorem 19, p. 618. Let `A′ = A − 𝟙 · µ(A)` (`center A`) with an arbitrary
SVD `A′ = U S Vᵀ`, let `m = min{n, d, j + ⌈j/ε⌉ − 1}`, `S′` the first `m` rows of `Σ^(m) Vᵀ`
(Algorithm 1 run on `A′`), `Δ = ‖A′ − A′^(m)‖²_F` and `S″ = √(m/n) · [S′; −S′]`. Then for every
`j`-dimensional linear subspace `L`,
`dist²(A′, L) ≤ (n/(2m)) · dist²(S″, L) + Δ ≤ (1 + ε) · dist²(A′, L)`. -/
theorem eq7_symmetrized_coreset {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
    (hA : ProjLikeRetr.FixedRank.IsSVD (center A) U S V) (hn : 1 ≤ n)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ L = j →
      TinyCoreset.DimRed.distSq (center A) (L : Set (EuclideanSpace ℝ (Fin d))) ≤
          affineWeight n (coresetSize n d j ε) *
              TinyCoreset.DimRed.distSq (affineCoresetRows n 0
                  (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
                (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
        affineWeight n (coresetSize n d j ε) *
              TinyCoreset.DimRed.distSq (affineCoresetRows n 0
                  (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
                (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ≤
          (1 + ε) * TinyCoreset.DimRed.distSq (center A) (L : Set (EuclideanSpace ℝ (Fin d))) := by sorry

end TinyCoreset.Affine
