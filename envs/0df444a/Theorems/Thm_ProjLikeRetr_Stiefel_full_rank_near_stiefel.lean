-- Prove2me | Theorems.Thm_ProjLikeRetr_Stiefel_full_rank_near_stiefel
-- name    : ProjLikeRetr.Stiefel.full_rank_near_stiefel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:46.637486+00:00
-- url     : https://prove2.me/theorems/8e798c06-9ef3-493a-bb58-013ab9bdeec6
-- title:
--   §3.3, proof of Prop. 3.4, p. 10 — if ‖X − X̄‖ < σ_m(X̄) with X̄ ∈ V_{n,m}, then X is full rank
-- statement:
--   Let $1\le m\le n$, let $\bar X\in V_{n,m}$ and let $X\in\mathbb R^{n\times m}$ satisfy
--
--   $$\|X-\bar X\|<\sigma_m(\bar X),$$
--
--   where $\|\cdot\|$ is the Frobenius norm and $\sigma_m$ the $m$-th largest singular value. Then $X$ has full rank: $\sigma_m(X)>0$ and $\operatorname{rank}X=m$.
--
--   Since the columns of $\bar X$ are orthonormal, $\sigma_m(\bar X)=1$, so the hypothesis says that $X$ lies in the open Frobenius ball of radius $1$ around $\bar X$. Full rank is what makes the polar decomposition of $X$, and hence the projection of Proposition 3.4, unique.
--
--   **Formalization Note** `sv` is 1-based; $\sigma_m(\bar X)$ is kept as `sv Xbar m` rather than replaced by its value $1$, as on the page. The hypothesis $0<m$ excludes the empty frame, for which $\sigma_m$ is meaningless; $m\le n$ is the page's standing assumption of §3.3.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3, proof of Proposition 3.4 (last sentence: 'the same arguments as in the beginning of the proof of Proposition 3.3 give that X is full rank')

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ProjLikeRetr_Stiefel_SVD

open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.Stiefel

/-- §3.3, proof of Proposition 3.4, p. 10: let `1 ≤ m ≤ n`, `X̄ ∈ V_{n,m}` (`Xbar`) and
`X ∈ ℝ^{n×m}` with `‖X − X̄‖ < σ_m(X̄)` (Frobenius norm, strict). Then `X` has full rank:
its `m`-th singular value is positive and `rank X = m`. -/
theorem full_rank_near_stiefel {n m : ℕ} (hmn : m ≤ n) (hm : 0 < m)
    (Xbar X : Matrix (Fin n) (Fin m) ℝ) (hXbar : Xbar ∈ stiefel n m)
    (hX : ‖X - Xbar‖ < ProjLikeRetr.FixedRank.sv Xbar m) :
    0 < ProjLikeRetr.FixedRank.sv X m ∧ X.rank = m := by sorry

end ProjLikeRetr.Stiefel
