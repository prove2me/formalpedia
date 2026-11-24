-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_tsp_exists
-- name    : RoughSurfaceScattering.dipole_tsp_exists
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:43:48.758481+00:00
-- url     : https://prove2.me/theorems/94a9b019-702b-4b17-8b33-e77971d1ecd1
-- title:
--   Existence of a TSP solution for an incident hypersingular point source
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$ describe the interface $\Gamma$ with upper region $D^+=\{x:x_2>f(x_1)\}$, and let $k_\pm,\mu>0$ satisfy
--
--   $$(\mu-1)(k_+^2-k_-^2\mu)\ge0,\qquad k_+^2\ne k_-^2\mu .$$
--
--   Let $z\in D^+$ and $\nu\in\mathbb R^2$. Then the Transmission Scattering Problem with incident hypersingular point source
--
--   $$u^i(x)=\nabla_x\Phi_{k_+}(x,z)\cdot\nu,$$
--
--   that is, with data $g_1=-u^i|_\Gamma$ and $g_2=-\partial_nu^i|_\Gamma$, has a solution $(u_+,u_-)$.
--
--   Since $z$ lies at positive distance from $\Gamma$, the data belong to $BC^{1,\alpha}(\Gamma)\times BC^{0,\alpha}(\Gamma)$, and Theorem 4.3 provides the solution. This is the existence of the singular solutions $(\tilde u_+^{(j)},\tilde u_-^{(j)})$ used in Theorem 5.3 and in Section 6.
--
--   **Formalization Note** Theorem 4.3 is formalized with $h_-<f^-<f^+<h_+$, which excludes a flat interface; this statement asks for existence for every $f\in BC^{1,1}$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 4.3 (PDF p. 16) applied to the data of the incident field ∇_x Φ_{k_+}(x, z)·ν; used for the hypersingular point sources of Theorem 5.3 (PDF p. 21) and Remark 5.4 (PDF p. 22: "the assumptions in Theorem 4.3 are used to only ensure the existence of the singular solutions").

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_tsp_exists (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ) (hpar : ParamCond kp km μ)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) :
    ∃ u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u.1 u.2 := by sorry

end RoughSurfaceScattering
