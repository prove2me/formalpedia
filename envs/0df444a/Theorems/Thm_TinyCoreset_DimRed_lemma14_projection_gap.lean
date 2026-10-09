-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_lemma14_projection_gap
-- name    : TinyCoreset.DimRed.lemma14_projection_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:22.103786+00:00
-- url     : https://prove2.me/theorems/171d2c75-8983-4b14-91d3-5b3a2f7426da
-- title:
--   Lemma 14, p. 613 — projected energy lost by SVD truncation
-- statement:
--   Fix any SVD $A=U\Sigma V^T$ of $A\in\mathbb R^{n\times d}$ and let $A^{(m)}=U\Sigma^{(m)}V^T$ retain its first $m$ diagonal entries. Let $1\le j\le d-1$, let $X\in\mathbb R^{d\times j}$ have orthonormal columns, and let $1\le m\le\min\{n,d\}-1$. Then
--
--   $$0\le\|AX\|_F^2-\|A^{(m)}X\|_F^2\le j\sigma_{m+1}^2.$$
--
--   This bounds the loss of projected squared norm using the next singular value of the chosen SVD.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 613, Lemma 14

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem lemma14_projection_gap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (hX : Xᵀ * X = 1)
    (m : ℕ) (hm1 : 1 ≤ m) (hmnd : m + 1 ≤ min n d) :
    0 ≤ frobSq (A * X) - frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * X) ∧
    frobSq (A * X) - frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * X) ≤
      (j : ℝ) * sigma S (m + 1) ^ 2 := by sorry

end TinyCoreset.DimRed
