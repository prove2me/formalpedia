-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_corollary16_subspace_coreset_bound
-- name    : TinyCoreset.DimRed.corollary16_subspace_coreset_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:58.672697+00:00
-- url     : https://prove2.me/theorems/6895ec32-78cb-4008-b0b4-2e5bf555bf80
-- title:
--   Corollary 16, p. 614 — multiplicative bound for residual-corrected subspace cost
-- statement:
--   Fix any SVD $A=U\Sigma V^T$ and let $A^{(m)}$ keep its first $m$ singular directions. Suppose $\varepsilon>0$, $1\le j\le d-1$, and $\lceil j/\varepsilon\rceil+j-1\le m\le\min\{n,d\}-1$. For every $Y\in\mathbb R^{d\times(d-j)}$ with orthonormal columns, with $\Delta=\|A-A^{(m)}\|_F^2$,
--
--   $$\|AY\|_F^2\le\|A^{(m)}Y\|_F^2+\Delta\le(1+\varepsilon)\|AY\|_F^2.$$
--
--   The residual-corrected truncation preserves all linear $j$-subspace costs within a multiplicative factor.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), pp. 614–615, Corollary 16 and display (2)

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem corollary16_subspace_coreset_bound {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : ⌈(j : ℝ) / ε⌉₊ + j ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    frobSq (A * Y) ≤ frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V) ∧
    frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V) ≤
        (1 + ε) * frobSq (A * Y) := by sorry

end TinyCoreset.DimRed
