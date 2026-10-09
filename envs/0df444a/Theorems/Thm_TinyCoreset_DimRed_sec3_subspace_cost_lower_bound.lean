-- Prove2me | Theorems.Thm_TinyCoreset_DimRed_sec3_subspace_cost_lower_bound
-- name    : TinyCoreset.DimRed.sec3_subspace_cost_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:28.737695+00:00
-- url     : https://prove2.me/theorems/d997e12f-6a0d-4c1e-af63-34ed0e7ebc44
-- title:
--   §3, p. 613 — lower bound on linear subspace cost
-- statement:
--   Fix any SVD $A=U\Sigma V^T$ of $A\in\mathbb R^{n\times d}$. Let $1\le j\le\min\{n,d\}-1$ and let $Y\in\mathbb R^{d\times(d-j)}$ have orthonormal columns. Then
--
--   $$\sum_{i=j+1}^{\min\{n,d\}}\sigma_i^2\le\|AY\|_F^2.$$
--
--   This is the lower bound for the cost of a linear $j$-dimensional subspace stated in §3. The paper also records attainment by the top $j$ right singular vectors; this item isolates the lower bound used later.
--
--   **Formalization Note** The bound $j+1\le\min\{n,d\}$ in Lean carries the range fixed at the opening of §3.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 613, §3, second paragraph ('Recall that …')

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

namespace TinyCoreset.DimRed

open scoped Matrix

theorem sec3_subspace_cost_lower_bound {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjnd : j + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    (∑ i ∈ Finset.Icc (j + 1) (min n d), sigma S i ^ 2) ≤ frobSq (A * Y) := by sorry

end TinyCoreset.DimRed
