-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_eq9_pythagoras_for_shapes
-- name    : TinyCoreset.DimRed.eq9_pythagoras_for_shapes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:26.000585+00:00
-- url     : https://prove2.me/theorems/257bbc7e-a4a7-4403-b3b2-4c011f697ad4
-- title:
--   (9), p. 620 — Pythagorean split of shape cost
-- statement:
--   Let $X\in\mathbb R^{d\times j}$ and $Y\in\mathbb R^{d\times(d-j)}$ have complementary orthonormal columns. Let $C\subseteq\mathbb R^d$ be nonempty and contained in the column space of $X$. For every data matrix $B\in\mathbb R^{n\times d}$,
--
--   $$\operatorname{dist}^2(B,C)=\|BY\|_F^2+\operatorname{dist}^2(BXX^T,C).$$
--
--   This separates the cost perpendicular to the span of $C$ from the cost of the projected rows inside that span. It applies to both $B=A$ and $B=A^{(m)}$ in the paper.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 620, display (9) and the preceding displayed line

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem eq9_pythagoras_for_shapes {n d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0)
    (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty)
    (hCX : C ⊆ LinearMap.range (Matrix.toEuclideanLin X)) :
    distSq B C = frobSq (B * Y) + distSq (B * X * Xᵀ) C := by sorry

end TinyCoreset.DimRed
