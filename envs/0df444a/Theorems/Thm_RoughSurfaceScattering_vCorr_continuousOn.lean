-- Prove2me | Theorems.Thm_RoughSurfaceScattering_vCorr_continuousOn
-- name    : RoughSurfaceScattering.vCorr_continuousOn
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:44:08.517143+00:00
-- url     : https://prove2.me/theorems/c6a94625-63e4-4868-98d9-f780e160a86f
-- title:
--   Continuity of the correction term $v_j$ of Theorem 5.3 in $D_0$
-- statement:
--   Let $D_0\subseteq\mathbb R^2$ be a bounded $C^{2,\lambda}$ domain, $\lambda\in(0,1]$, with outward unit normal $n$ and arc length $ds$ on $\partial D_0$. Let $n_0\in\mathbb R^2$, $\mu\in\mathbb R$, and let $x_j,y_j\notin\partial D_0$. Then the function
--
--   $$v(x)=\frac{2\mu(1-\mu)}{(\mu+1)^2}\int_{\partial D_0}\frac{\partial\Phi_0(x,y)}{\partial n(y)}\big(\nabla_x\Phi_0(y,x_j)+\nabla_x\Phi_0(y,y_j)\big)\cdot n_0\,ds(y)$$
--
--   is continuous on $D_0$.
--
--   This is the correction term $v_j$ of Theorem 5.3, a double-layer potential of the Laplacian whose density is continuous on $\partial D_0$ because the poles $x_j,y_j$ are off the boundary. Continuity (hence measurability) of $v_j$ is what allows its $L^2(D_0)$ bound from Theorem 5.3 to be combined with other estimates by the triangle inequality.
--
--   **Formalization Note** $ds$ is the one-dimensional Hausdorff measure restricted to the frontier of $D_0$, and $n$ is `outwardNormal D0`, exactly as in the definition `vCorr`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3, PDF p. 21, definition of v_j (a double-layer potential of the Laplacian over ∂D_0 with density (∇_x Φ_0(y, x_j) + ∇_x Φ_0(y, y_j))·n(x_0)).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem vCorr_continuousOn (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (μ : ℝ) (D0 : Set R2)
    (hD0 : IsC2LambdaDomain lam D0) (n0 xj yj : R2) (hxj : xj ∉ frontier D0)
    (hyj : yj ∉ frontier D0) :
    ContinuousOn (vCorr μ D0 n0 xj yj) D0 := by sorry

end RoughSurfaceScattering
