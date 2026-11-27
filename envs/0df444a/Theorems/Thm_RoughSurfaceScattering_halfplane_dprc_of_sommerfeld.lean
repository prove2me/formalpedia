-- Prove2me | Theorems.Thm_RoughSurfaceScattering_halfplane_dprc_of_sommerfeld
-- name    : RoughSurfaceScattering.halfplane_dprc_of_sommerfeld
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:01:44.138282+00:00
-- url     : https://prove2.me/theorems/9893c34e-6187-4804-8b95-1ff0cd90ea00
-- title:
--   Radiating Helmholtz solutions below $\Gamma_h$ are double-layer potentials of their trace
-- statement:
--   Let $k>0$, $h<z_2$, and let $v$ be $C^2$ and solve $\Delta v+k^2v=0$ in $\{x_2<z_2\}$. Suppose that for $x_2\le h$ and $|x-z|\ge1$,
--   $$|v|,\ \|\nabla v\|\le C|x-z|^{-1/2},\qquad\big|\partial_rv-ikv\big|\le C|x-z|^{-3/2}\quad(r=|x-z|).$$
--   Then for every $x\in U_h^-$,
--   $$v(x)=-2\int_{\mathbb R}\frac{\partial\Phi_k(x,y)}{\partial y_2}\Big|_{y=(t,h)}v(t,h)\,dt .$$
--   This is Green's representation in $U_h^-$ with the Dirichlet Green's function $\Phi_k(x,y)-\Phi_k(x,y'_h)$. The contribution of large half circles vanishes by the Sommerfeld condition.
--
--   **Formalization Note** The kernel and the sign are those of the platform's `IsDPRC`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Lemma 2.4 and Remark 2.5 (pp. 9-10), from [22] (Chandler-Wilde and Zhang).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem halfplane_dprc_of_sommerfeld (k : ℝ) (hk : 0 < k) (h : ℝ) (z : R2) (hz : h < z 1)
    (v : R2 → ℂ) (hv : ContDiffOn ℝ 2 v {x | x 1 < z 1})
    (hH : IsHelmholtzOn {x | x 1 < z 1} k v)
    (hdec : ∃ C : ℝ, ∀ x : R2, x 1 ≤ h → 1 ≤ ‖x - z‖ →
      ‖v x‖ ≤ C * ‖x - z‖ ^ (-(1 / 2 : ℝ)) ∧
      ‖fderiv ℝ v x‖ ≤ C * ‖x - z‖ ^ (-(1 / 2 : ℝ)) ∧
      ‖fderiv ℝ v x (‖x - z‖⁻¹ • (x - z)) - Complex.I * k * v x‖ ≤ C * ‖x - z‖ ^ (-(3 / 2 : ℝ))) :
    ∀ x ∈ Uminus h, v x = -2 * ∫ t, dPhi_dy2 k x (pt t h) * v (pt t h) := by sorry

end RoughSurfaceScattering
