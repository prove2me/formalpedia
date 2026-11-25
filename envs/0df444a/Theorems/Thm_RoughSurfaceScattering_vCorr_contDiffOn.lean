-- Prove2me | Theorems.Thm_RoughSurfaceScattering_vCorr_contDiffOn
-- name    : RoughSurfaceScattering.vCorr_contDiffOn
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T00:31:57.509681+00:00
-- url     : https://prove2.me/theorems/686323ff-7e76-4a3d-839a-bc5cba5ed77f
-- title:
--   The correction $v_j$ of Theorem 5.3 is $C^1$ in $D_0$
-- statement:
--   Let $D_0$ be a bounded $C^{2,\lambda}$ domain and $x_j,y_j\notin\partial D_0$. Then the function
--
--   $$v_j(x)=\frac{2\mu(1-\mu)}{(\mu+1)^2}\int_{\partial D_0}\frac{\partial\Phi_0(x,y)}{\partial n(y)}\,\big(\nabla_x\Phi_0(y,x_j)+\nabla_x\Phi_0(y,y_j)\big)\cdot n(x_0)\,ds(y)$$
--
--   is $C^1$ in $D_0$. Points of $D_0$ are at positive distance from $\partial D_0$, where the kernel is smooth in $x$. The density is bounded on $\partial D_0$ because $x_j,y_j\notin\partial D_0$, and $\partial D_0$ has finite length. So one may differentiate under the integral sign. This strengthens the proved `vCorr_continuousOn`.
--
--   **Formalization Note** $v_j$ is the platform's `vCorr`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3 and its proof, PDF pp. 21-22 (definition of v_j, p. 21).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem vCorr_contDiffOn (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (μ : ℝ) (D0 : Set R2)
    (hD0 : IsC2LambdaDomain lam D0) (n0 xj yj : R2) (hxj : xj ∉ frontier D0)
    (hyj : yj ∉ frontier D0) :
    ContDiffOn ℝ 1 (vCorr μ D0 n0 xj yj) D0 := by sorry

end RoughSurfaceScattering
