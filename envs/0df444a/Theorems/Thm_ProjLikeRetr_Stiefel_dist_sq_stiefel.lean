-- Prove2me | Theorems.Thm_ProjLikeRetr_Stiefel_dist_sq_stiefel
-- name    : ProjLikeRetr.Stiefel.dist_sq_stiefel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:30.814184+00:00
-- url     : https://prove2.me/theorems/5c936dc8-c9f4-4f91-a5a5-83f9a73beef2
-- title:
--   §3.3, proof of Prop. 3.4, p. 10 — ‖X − Y‖² = ‖X‖² + m − 2 trace(YᵀX) for Y ∈ V_{n,m}
-- statement:
--   Let $X\in\mathbb R^{n\times m}$ and let $\|\cdot\|$ be the Frobenius norm, $\|X\|^2=\sum_{i,j}X_{ij}^2=\operatorname{trace}(X^\top X)$. For every $Y$ in the Stiefel manifold $V_{n,m}=\{Y: Y^\top Y=I_m\}$,
--
--   $$\|X-Y\|^2=\|X\|^2+m-2\operatorname{trace}(Y^\top X).$$
--
--   The identity reduces the projection of $X$ onto $V_{n,m}$ to the maximization of the linear function $Y\mapsto\operatorname{trace}(Y^\top X)$ over $V_{n,m}$, which is the first step of the proof of Proposition 3.4.
--
--   **Formalization Note** The page prints the constant as $m^2$. Since $\|Y\|^2=\operatorname{trace}(Y^\top Y)=\operatorname{trace}(I_m)=m$, the correct constant is $m$; with $m^2$ the identity is false for every $m\ge2$ (take $X=Y$). The statement uses $m$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3, proof of Proposition 3.4 (first sentence; the page's m² is a misprint for m)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel

open scoped Matrix Matrix.Norms.Frobenius

namespace ProjLikeRetr.Stiefel

/-- §3.3, proof of Proposition 3.4, p. 10: for every real `n × m` matrix `X` and every
`Y ∈ V_{n,m}`, `‖X − Y‖² = ‖X‖² + m − 2 trace(YᵀX)` in the Frobenius norm. The page prints
`m²`; since `‖Y‖² = trace(YᵀY) = trace(I_m) = m`, the correct constant is `m` (with `m²` the
identity fails for `m ≥ 2`). -/
theorem dist_sq_stiefel {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℝ) (hY : Y ∈ stiefel n m) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + (m : ℝ) - 2 * (Yᵀ * X).trace := by sorry

end ProjLikeRetr.Stiefel
