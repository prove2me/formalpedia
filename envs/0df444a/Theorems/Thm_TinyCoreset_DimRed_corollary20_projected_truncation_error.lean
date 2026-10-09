-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_corollary20_projected_truncation_error
-- name    : TinyCoreset.DimRed.corollary20_projected_truncation_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:26.947801+00:00
-- url     : https://prove2.me/theorems/3dd4db44-b4ed-4858-bf59-00009b0e5ab1
-- title:
--   Corollary 20, p. 619 — projected truncation error relative to subspace cost
-- statement:
--   Fix any SVD $A=U\Sigma V^T$. Suppose $\varepsilon>0$, $1\le j\le d-1$, and $j+\lceil j/\varepsilon\rceil-1\le m\le\min\{n,d\}-1$. Let $X\in\mathbb R^{d\times j}$ have orthonormal columns, and let $Y\in\mathbb R^{d\times(d-j)}$ have orthonormal columns spanning the complement of the column space of $X$. Then
--
--   $$0\le\|AXX^T-A^{(m)}XX^T\|_F^2\le\varepsilon\|AY\|_F^2.$$
--
--   The projection of the truncated data stays close to the projection of the original data, measured against the discarded subspace cost.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 619, Corollary 20

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem corollary20_projected_truncation_error {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : ⌈(j : ℝ) / ε⌉₊ + j ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0) :
    0 ≤ frobSq (A * X * Xᵀ - ProjLikeRetr.FixedRank.truncSVD m U S V * X * Xᵀ) ∧
    frobSq (A * X * Xᵀ - ProjLikeRetr.FixedRank.truncSVD m U S V * X * Xᵀ) ≤
      ε * frobSq (A * Y) := by sorry

end TinyCoreset.DimRed
