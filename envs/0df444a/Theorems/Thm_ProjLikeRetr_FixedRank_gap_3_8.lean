-- Prove2me | Theorems.Thm_ProjLikeRetr_FixedRank_gap_3_8
-- name    : ProjLikeRetr.FixedRank.gap_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:03:25.236901+00:00
-- url     : https://prove2.me/theorems/73c22a99-2977-45d3-a309-20783ba39eb9
-- title:
--   (3.8), proof of Prop. 3.3, p. 9 — σ_{r+1}(X) < σ_r(X̄)/2 < σ_r(X)
-- statement:
--   Let $r\ge1$, let $\bar X\in\mathbb R^{n\times m}$ have rank exactly $r$, and let $X\in\mathbb R^{n\times m}$ satisfy $\|X-\bar X\|<\sigma_r(\bar X)/2$, where $\|\cdot\|$ is the Frobenius norm and $\sigma_i$ the $i$-th largest singular value. Then
--
--   $$\sigma_{r+1}(X)<\frac{\sigma_r(\bar X)}{2}<\sigma_r(X).$$
--
--   In particular $X$ has a strict gap $\sigma_r(X)>\sigma_{r+1}(X)$ and $\sigma_r(X)>0$. In the proof of Proposition 3.3 this gap yields both that the truncated decomposition of $X$ has rank exactly $r$ and that the projection onto the matrices of rank at most $r$ is unique.
--
--   **Formalization Note** `sv` is 1-based, so $\sigma_r$ needs $r\ge1$; this is the hypothesis $0<r$. The radius $\sigma_r(\bar X)/2$ and the strict inequality are those of Proposition 3.3 and (3.8).
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 9, §3.2, proof of Proposition 3.3, display (3.8)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_FixedRank_rankSet
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.FixedRank

/-- (3.8), proof of Proposition 3.3, p. 9: let `r ≥ 1`, let `X̄` (`Xbar`) have rank `r`, and let
`‖X − X̄‖ < σ_r(X̄)/2` (Frobenius norm). Then `σ_{r+1}(X) < σ_r(X̄)/2 < σ_r(X)`. -/
theorem gap_3_8 {n m : ℕ} (r : ℕ) (hr : 0 < r) (Xbar X : Matrix (Fin n) (Fin m) ℝ)
    (hXbar : Xbar ∈ rankSet r) (hX : ‖X - Xbar‖ < sv Xbar r / 2) :
    sv X (r + 1) < sv Xbar r / 2 ∧ sv Xbar r / 2 < sv X r := by sorry

end ProjLikeRetr.FixedRank
