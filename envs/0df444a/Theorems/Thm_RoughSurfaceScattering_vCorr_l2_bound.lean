-- Prove2me | Theorems.Thm_RoughSurfaceScattering_vCorr_l2_bound
-- name    : RoughSurfaceScattering.vCorr_l2_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T05:54:35.552795+00:00
-- url     : https://prove2.me/theorems/8de59df9-b796-5af8-9b46-ce80dbd13cf3
-- title:
--   The correction $v_j$ of Theorem 5.3 is bounded in $L^2(D_0)$ uniformly in $j$
-- statement:
--   Let $x_0=(s_0,f(s_0))$, $x_j=x_0-(\delta/j)n(x_0)$ and $y_j=x_0+(\delta/j)n(x_0)$. For $\delta$ small and a bounded $C^{2,\lambda}$ domain $D_0$ with $B_{2\delta}(x_0)\cap D_-\subseteq D_0\subseteq D_-$, the functions
--
--   $$v_j(x)=\frac{2\mu(1-\mu)}{(\mu+1)^2}\int_{\partial D_0}\frac{\partial\Phi_0(x,y)}{\partial n(y)}\,\big(\nabla_x\Phi_0(y,x_j)+\nabla_x\Phi_0(y,y_j)\big)\cdot n(x_0)\,ds(y)$$
--
--   satisfy $\|v_j\|_{L^2(D_0)}\le C$ uniformly in $j$.
--
--   *Proof idea (paper).* The density $\phi_j=(\nabla\Phi_0(\cdot,x_j)+\nabla\Phi_0(\cdot,y_j))\cdot n(x_0)$ is uniformly bounded on $\partial D_0$: near $x_0$ the singularities of the mirror pair $x_j,y_j$ cancel. By duality, $\|v_j\|_{L^2(D_0)}$ is controlled by
--   $$\sup_{\|g\|_{L^2}=1}\Big\|\partial_{n(y)}\int_{D_0}\Phi_0(x,y)g(x)\,dx\Big\|_{L^1(\partial D_0)}\,\|\phi_j\|_{L^\infty(\partial D_0)}\le C .$$
--   This uses that the volume potential maps $L^2(D_0)$ into $H^2(D_0)$ boundedly, and that the trace maps $H^2(D_0)$ into $L^1(\partial D_0)$.
--
--   **Formalization Note** $v_j$ is `vCorr` and the norm is `l2Norm`. This is the $L^2$ conjunct of `dipole_core_bound`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3 and its proof, PDF pp. 21-22 (last part of the proof, p. 22: duality and the volume potential).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem vCorr_l2_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (μ : ℝ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            l2Norm D0 (vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
