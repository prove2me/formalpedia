-- Prove2me | Theorems.Thm_ProjLikeRetr_FixedRank_eckart_young_unique
-- name    : ProjLikeRetr.FixedRank.eckart_young_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:03:19.113402+00:00
-- url     : https://prove2.me/theorems/b95a2724-3620-4df6-adcc-78e54fdc0acf
-- title:
--   §3.2, proof of Prop. 3.3, p. 10 — the projection onto {rank ≤ r} is unique when σ_r(X) > σ_{r+1}(X)
-- statement:
--   Let $r\ge1$, let $X\in\mathbb R^{n\times m}$, and let $X=U\Sigma V^\top$ be a singular value decomposition (3.5) of $X$ with $U=[u_1,\dots,u_n]$, $V=[v_1,\dots,v_m]$. If
--
--   $$\sigma_r(X)>\sigma_{r+1}(X),$$
--
--   then the truncated decomposition $\hat X=\sum_{i=1}^r\sigma_i(X)u_iv_i^\top$ is the **unique** nearest matrix to $X$ among the matrices of rank at most $r$ (Frobenius norm): the set of nearest points is exactly $\{\hat X\}$.
--
--   Without the gap the nearest point is in general not unique (for $X=I_2$ and $r=1$, every $uu^\top$ with $\|u\|=1$ is a nearest rank-one matrix). The paper cites this uniqueness from Helmke and Moore [13, §5.1 Cor. 1.17] and [18]; with (3.8) it gives the uniqueness part of Proposition 3.3.
--
--   **Formalization Note** `sv` is 1-based, so the hypotheses are $0<r$ and `sv X (r + 1) < sv X r`. The conclusion is the set equality `{Y | IsMetricProjection (rankLeSet r) X Y} = {truncSVD r U S V}`, for the given (arbitrary) singular value decomposition.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, pp. 9–10, §3.2, proof of Proposition 3.3 (citing [13, §5.1 Cor. 1.17], [18])

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_FixedRank_rankSet
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.FixedRank

/-- §3.2, proof of Proposition 3.3, p. 10 (citing [13, §5.1 Cor. 1.17], [18]): uniqueness of the
projection onto `{rank(Y) ≤ r}` under the gap `σ_r(X) > σ_{r+1}(X)`. If `r ≥ 1`, `X = U S Vᵀ` is
a singular value decomposition (3.5) of `X ∈ ℝ^{n×m}` and `σ_{r+1}(X) < σ_r(X)`, then the
truncated SVD `Σ_{i=1}^r σ_i(X) u_i v_iᵀ` is the unique nearest matrix of rank at most `r` to `X`
(Frobenius norm). -/
theorem eckart_young_unique {n m : ℕ} (r : ℕ) (hr : 0 < r) (X : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : IsSVD X U S V) (hgap : sv X (r + 1) < sv X r) :
    {Y | IsMetricProjection (rankLeSet r) X Y} = {truncSVD r U S V} := by sorry

end ProjLikeRetr.FixedRank
