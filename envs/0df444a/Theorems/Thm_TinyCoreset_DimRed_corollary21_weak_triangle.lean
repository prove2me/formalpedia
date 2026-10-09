-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_corollary21_weak_triangle
-- name    : TinyCoreset.DimRed.corollary21_weak_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:25.582132+00:00
-- url     : https://prove2.me/theorems/a2ac286b-9d2a-4288-833a-e6616f5af3ca
-- title:
--   Corollary 21, p. 619 — weak triangle bound for squared shape costs
-- statement:
--   Let $\varepsilon>0$, let $A,B\in\mathbb R^{n\times d}$, and let $C\subseteq\mathbb R^d$ be nonempty. Then
--
--   $$|\operatorname{dist}^2(A,C)-\operatorname{dist}^2(B,C)|\le\varepsilon\operatorname{dist}^2(A,C)+(1+1/\varepsilon)\|A-B\|_F^2.$$
--
--   This bounds how much a shape-fitting cost can change when every data point is perturbed.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), pp. 619–620, Corollary 21 and display (8)

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem corollary21_weak_triangle {n d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (A B : Matrix (Fin n) (Fin d) ℝ)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) :
    |distSq A C - distSq B C| ≤ ε * distSq A C + (1 + 1 / ε) * frobSq (A - B) := by sorry

end TinyCoreset.DimRed
