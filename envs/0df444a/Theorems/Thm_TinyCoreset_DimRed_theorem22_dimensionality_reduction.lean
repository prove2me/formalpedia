-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_theorem22_dimensionality_reduction
-- name    : TinyCoreset.DimRed.theorem22_dimensionality_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:32.545307+00:00
-- url     : https://prove2.me/theorems/c8962cd9-6caf-4034-8e26-a32ffd85b95f
-- title:
--   Theorem 22, p. 620 — SVD truncation plus residual preserves every j-dimensional shape cost
-- statement:
--   Fix any SVD $A=U\Sigma V^T$ of $A\in\mathbb R^{n\times d}$, and let $A^{(m)}=U\Sigma^{(m)}V^T$ keep the first $m$ diagonal entries. Let $1\le j\le d-1$, $0<\varepsilon\le1$, and $\lceil8j/\varepsilon^2\rceil-1\le m\le\min\{n,d\}-1$. For every nonempty set $C\subseteq\mathbb R^d$ contained in a linear $j$-dimensional subspace,
--
--   $$\left|\bigl(\operatorname{dist}^2(A^{(m)},C)+\|A-A^{(m)}\|_F^2\bigr)-\operatorname{dist}^2(A,C)\right|\le\varepsilon\operatorname{dist}^2(A,C).$$
--
--   Thus a rank-$m$ representation together with one residual scalar preserves the fitting cost of every allowed shape at once. The statement applies to arbitrary nonempty shapes inside a linear subspace, including finite sets of centers.
--
--   **Formalization Note** The threshold is the theorem's printed $\lceil8j/\varepsilon^2\rceil-1$, even though one step of the printed proof invokes earlier results under a stronger threshold. The SVD is arbitrary, including when singular values tie.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 620, Theorem 22; proof pp. 620–621

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem theorem22_dimensionality_reduction {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j m : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hm : ⌈8 * (j : ℝ) / ε ^ 2⌉₊ ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty)
    (hCL : ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
      Module.finrank ℝ L = j ∧ C ⊆ L) :
    |(distSq (ProjLikeRetr.FixedRank.truncSVD m U S V) C +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V)) - distSq A C| ≤
      ε * distSq A C := by sorry

end TinyCoreset.DimRed
