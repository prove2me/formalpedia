-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_dprc_representation
-- name    : RoughSurfaceScattering.phi_dprc_representation
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T08:39:06.362501+00:00
-- url     : https://prove2.me/theorems/69308841-eaac-55a8-a5ee-c02e2c358f72
-- title:
--   Downward radiation representation of $\Phi_k(\cdot,z)$ below $\Gamma_h$, $h<z_2$
-- statement:
--   Let $k>0$, $z\in\mathbb R^2$ and $h<z_2$. There is $\varphi\in L^\infty(\mathbb R)$ such that
--
--   $$\Phi_k(x,z)=-2\int_{\mathbb R}\frac{\partial\Phi_k(x,y)}{\partial y_2}\Big|_{y=(t,h)}\varphi(t)\,dt\qquad\text{for all }x\in U_h^-,$$
--
--   which is the downward propagating radiation condition (DPRC) of Definition 2.2. Since $\Phi_k(\cdot,z)$ is a radiating solution of the Helmholtz equation in $U_h^-$, bounded with bounded trace on $\Gamma_h$, Lemma 2.4 gives this representation with $\varphi(t)=\Phi_k((t,h),z)$ (Remark 2.5).
--
--   **Formalization Note** The kernel is the platform's `dPhi_dy2`, and $U_h^-$ is `Uminus h`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Lemma 2.4 and Remark 2.5 (pp. 9-10), applied to Φ_k(·,z) in the half plane below the source.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_dprc_representation (k : ℝ) (hk : 0 < k) (z : R2) (h : ℝ) (hh : h < z 1) :
    ∃ φ : ℝ → ℂ, MemLp φ ⊤ volume ∧
      ∀ x ∈ Uminus h, Phi k x z = -2 * ∫ t, dPhi_dy2 k x (pt t h) * φ t := by sorry

end RoughSurfaceScattering
