-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_lemma15_residual_sandwich
-- name    : TinyCoreset.DimRed.lemma15_residual_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:28.331057+00:00
-- url     : https://prove2.me/theorems/be5d4aeb-c347-4799-bc59-d8524e64eae3
-- title:
--   Lemma 15, p. 614 — residual-corrected subspace cost
-- statement:
--   Fix any SVD $A=U\Sigma V^T$ of $A\in\mathbb R^{n\times d}$ and its truncation $A^{(m)}$. Let $1\le j\le d-1$, $1\le m\le\min\{n,d\}-1$, and let $Y\in\mathbb R^{d\times(d-j)}$ have orthonormal columns. Writing $\Delta=\|A-A^{(m)}\|_F^2$, the corrected cost satisfies
--
--   $$0\le(\|A^{(m)}Y\|_F^2+\Delta)-\|AY\|_F^2\le j\sigma_{m+1}^2.$$
--
--   The residual term makes the truncated matrix an upper approximation to each linear subspace cost, with a quantified excess.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 614, Lemma 15

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem lemma15_residual_sandwich {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (m : ℕ) (hm1 : 1 ≤ m) (hmnd : m + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    0 ≤ (frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V)) - frobSq (A * Y) ∧
    (frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V)) - frobSq (A * Y) ≤
      (j : ℝ) * sigma S (m + 1) ^ 2 := by sorry

end TinyCoreset.DimRed
