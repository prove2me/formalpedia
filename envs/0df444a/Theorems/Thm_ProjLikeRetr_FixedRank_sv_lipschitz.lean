-- Prove2me | Theorems.Thm_ProjLikeRetr_FixedRank_sv_lipschitz
-- name    : ProjLikeRetr.FixedRank.sv_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:03:08.840892+00:00
-- url     : https://prove2.me/theorems/29fcc707-ffe0-4f1f-bd68-c51341346e4f
-- title:
--   §3.2, proof of Prop. 3.3, p. 9 — Weyl's bound |σ_i(X̄) − σ_i(X)| ≤ ‖X − X̄‖
-- statement:
--   Let $\bar X, X\in\mathbb R^{n\times m}$ and let $\|\cdot\|$ be the Frobenius norm, $\|X\|^2=\sum_{i,j}X_{ij}^2$. For every index $i\ge1$,
--
--   $$|\sigma_i(\bar X)-\sigma_i(X)|\le\|X-\bar X\|,$$
--
--   where $\sigma_i$ denotes the $i$-th largest singular value (zero for $i>\min\{n,m\}$).
--
--   Singular values are thus 1-Lipschitz functions of the matrix. In the proof of Proposition 3.3 this bound, cited from Horn and Johnson [20, 7.3.8], is what transfers the gap of $\bar X$ (whose $(r+1)$-st singular value vanishes) to the nearby matrix $X$ in (3.8).
--
--   **Formalization Note** `sv` is 1-based; the hypothesis $1\le i$ excludes the index $0$, which has no meaning on the page. The norm is Mathlib's Frobenius norm on matrices (`Matrix.Norms.Frobenius`).
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 9, §3.2, proof of Proposition 3.3 (citing [20, 7.3.8])

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_FixedRank_rankSet
import Definitions.Def_ProjLikeRetr_FixedRank_SVD

open RandomGradFree.Nonsmooth
open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.FixedRank

/-- §3.2, proof of Proposition 3.3, p. 9 (citing [20, 7.3.8], Weyl's perturbation bound): for all
real `n × m` matrices `X̄` (`Xbar`) and `X` and every 1-based index `i ≥ 1`,
`|σ_i(X̄) − σ_i(X)| ≤ ‖X − X̄‖`, where `‖·‖` is the Frobenius norm. -/
theorem sv_lipschitz {n m : ℕ} (Xbar X : Matrix (Fin n) (Fin m) ℝ) (i : ℕ) (hi : 1 ≤ i) :
    |sv Xbar i - sv X i| ≤ ‖X - Xbar‖ := by sorry

end ProjLikeRetr.FixedRank
