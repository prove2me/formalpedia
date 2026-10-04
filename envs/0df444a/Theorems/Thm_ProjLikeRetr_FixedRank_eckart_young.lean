-- Prove2me | Theorems.Thm_ProjLikeRetr_FixedRank_eckart_young
-- name    : ProjLikeRetr.FixedRank.eckart_young
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:02:52.271445+00:00
-- url     : https://prove2.me/theorems/006c54fe-c763-4b17-8e29-9d94995dfd72
-- title:
--   (3.7), p. 9 — Eckart–Young: the truncated SVD is a nearest matrix of rank at most r
-- statement:
--   Let $X\in\mathbb R^{n\times m}$, let $X=U\Sigma V^\top$ be a singular value decomposition (3.5) of $X$ with $U=[u_1,\dots,u_n]$, $V=[v_1,\dots,v_m]$, and let $r\ge0$. Then the truncated decomposition
--
--   $$\hat X=\sum_{i=1}^r\sigma_i(X)\,u_iv_i^\top$$
--
--   has rank at most $r$ and is a nearest matrix to $X$ among all matrices of rank at most $r$ in the Frobenius norm:
--
--   $$\|X-\hat X\|\le\|X-Y\|\qquad\text{for every }Y\in\mathbb R^{n\times m}\text{ with }\operatorname{rank}(Y)\le r.$$
--
--   This is the Eckart–Young theorem. It holds for every singular value decomposition of $X$, with no gap condition on the singular values, and it is the starting point of the proof of Proposition 3.3.
--
--   **Formalization Note** $\hat X$ is `truncSVD r U S V` (the diagonal entries of `S` play the role of $\sigma_i(X)$). "Nearest matrix" is the platform predicate `IsMetricProjection` for the set `rankLeSet r` under the Frobenius norm: membership in the set together with the distance inequality above. No uniqueness is claimed here; uniqueness under a gap is a separate milestone.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 9, §3.2, display (3.7) (Eckart–Young, citing [9], [20, §7.4.1])

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_FixedRank_rankSet
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.FixedRank

/-- (3.7), §3.2, p. 9 (Eckart–Young): if `X = U S Vᵀ` is a singular value decomposition (3.5) of
`X ∈ ℝ^{n×m}`, then the truncated SVD `X̂ = Σ_{i=1}^r σ_i(X) u_i v_iᵀ` is a nearest matrix (in the
Frobenius norm) to `X` among the matrices of rank at most `r`. -/
theorem eckart_young {n m : ℕ} (r : ℕ) (X : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : IsSVD X U S V) :
    IsMetricProjection (rankLeSet r) X (truncSVD r U S V) := by sorry

end ProjLikeRetr.FixedRank
