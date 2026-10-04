-- Prove2me | Theorems.Thm_ProjLikeRetr_FixedRank_projection_fixed_rank
-- name    : ProjLikeRetr.FixedRank.projection_fixed_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:03:34.584433+00:00
-- url     : https://prove2.me/theorems/e8a91437-4fc7-4613-9bd6-4213fee9951c
-- title:
--   Proposition 3.3, p. 9 — near a rank-r matrix the truncated SVD is the unique projection onto ℛ_r
-- statement:
--   Let $r\ge1$ and let $\mathcal R_r=\{X\in\mathbb R^{n\times m}:\operatorname{rank}(X)=r\}$, with $\mathbb R^{n\times m}$ equipped with the Frobenius norm. Let $\bar X\in\mathcal R_r$ and let $X\in\mathbb R^{n\times m}$ satisfy
--
--   $$\|X-\bar X\|<\frac{\sigma_r(\bar X)}{2}.$$
--
--   Then the projection of $X$ onto $\mathcal R_r$ exists, is unique, and for any singular value decomposition $X=U\Sigma V^\top$ (3.5), with $U=[u_1,\dots,u_n]$ and $V=[v_1,\dots,v_m]$, it is
--
--   $$P_{\mathcal R_r}(X)=\sum_{i=1}^r\sigma_i(X)\,u_iv_i^\top .$$
--
--   That is, the set of points of $\mathcal R_r$ nearest to $X$ is exactly the singleton $\{\sum_{i=1}^r\sigma_i(X)u_iv_i^\top\}$.
--
--   Although $\mathcal R_r$ is not closed, near any of its points the nearest-point map onto it is single valued and given by the truncated singular value decomposition. Combined with Proposition 3.2 of the paper, this makes $(X,Z)\mapsto P_{\mathcal R_r}(X+Z)$ an explicitly computable retraction on the manifold of fixed-rank matrices.
--
--   **Formalization Note** `sv` is 1-based, so $\sigma_r$ needs $r\ge1$: the hypothesis $0<r$ is added and is the only hypothesis not on the page ($\mathcal R_0=\{0\}$ has no $\sigma_0$). The conclusion `{Y | IsMetricProjection (rankSet r) X Y} = {truncSVD r U S V}` says existence, uniqueness and the formula at once, and holds for whichever singular value decomposition `(U, S, V)` of $X$ is given.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 9, §3.2, Proposition 3.3

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_FixedRank_rankSet
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.FixedRank

/-- Proposition 3.3, p. 9 (Projection onto the manifold of fixed-rank matrices): let `r ≥ 1` and
`X̄ ∈ ℛ_r` (`Xbar`); for any `X` with `‖X − X̄‖ < σ_r(X̄)/2` (Frobenius norm) and any singular value
decomposition (3.5) `X = U S Vᵀ`, the projection of `X` onto `ℛ_r` exists, is unique, and equals
`P_{ℛ_r}(X) = Σ_{i=1}^r σ_i(X) u_i v_iᵀ`: the set of nearest points of `ℛ_r` to `X` is exactly the
singleton of the truncated SVD. -/
theorem projection_fixed_rank {n m : ℕ} (r : ℕ) (hr : 0 < r) (Xbar X : Matrix (Fin n) (Fin m) ℝ)
    (hXbar : Xbar ∈ rankSet r) (hX : ‖X - Xbar‖ < sv Xbar r / 2)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : IsSVD X U S V) :
    {Y | IsMetricProjection (rankSet r) X Y} = {truncSVD r U S V} := by sorry

end ProjLikeRetr.FixedRank
