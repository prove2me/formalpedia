-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_claim3_pythagoras
-- name    : TinyCoreset.DimRed.claim3_pythagoras
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:58:06.36814+00:00
-- url     : https://prove2.me/theorems/56cad6c7-9699-4f37-9978-f500e90ca210
-- title:
--   Claim 3, p. 604 — Frobenius Pythagoras for complementary orthonormal columns
-- statement:
--   Let $X\in\mathbb R^{d\times j}$ and $Y\in\mathbb R^{d\times(d-j)}$ have orthonormal columns spanning complementary orthogonal subspaces. For every $A\in\mathbb R^{n\times d}$,
--
--   $$\|A\|_F^2=\|AX\|_F^2+\|AY\|_F^2.$$
--
--   This identity splits the energy of a matrix between a subspace and its orthogonal complement.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 604, Claim 3

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem claim3_pythagoras {n d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0)
    (A : Matrix (Fin n) (Fin d) ℝ) :
    frobSq A = frobSq (A * X) + frobSq (A * Y) := by sorry

end TinyCoreset.DimRed
