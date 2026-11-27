-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_data_holder
-- name    : RoughSurfaceScattering.dipole_data_holder
-- status  : Proved
-- author  : @もち
-- created : 2026-11-26T15:13:25.868876+00:00
-- url     : https://prove2.me/theorems/43dea653-38c3-5bdf-94d3-3bb15c48f24d
-- title:
--   The TSP data of a dipole source above $\Gamma$ lie in $BC^{1,1/2}(\Gamma)\times BC^{0,1/2}(\Gamma)$
-- statement:
--   Let $f\in BC^{1,1}$, $k>0$, $z\in D^+$ and $\nu\in\mathbb R^2$. For the incident dipole $u^i=\nabla_x\Phi_k(\cdot,z)\cdot\nu$, the TSP data
--   $$g_1=-u^i|_\Gamma\in BC^{1,1/2}(\Gamma),\qquad g_2=-\partial_nu^i|_\Gamma\in BC^{0,1/2}(\Gamma).$$
--
--   The point $z$ has positive distance from $\Gamma$, so $u^i$ is smooth near $\Gamma$, and its derivatives up to order three are bounded there (decay of Hankel functions). Together with $f'$ Lipschitz, this gives the required boundedness and Hölder continuity: Lipschitz for nearby points and boundedness for distant ones.
--
--   **Formalization Note** The exponent is $\alpha=1/2$; any $\alpha\in(0,1)$ would do.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 5 (the incident dipole ∇_xΦ_{k_+}(x,z)·ν, p. 21) and Theorem 4.3.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_data_holder (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (k : ℝ) (hk : 0 < k)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) :
    IsBC1AlphaGam f (1 / 2) (incData f (dipoleSource k z ν)).1 ∧
      IsBC0AlphaGam f (1 / 2) (incData f (dipoleSource k z ν)).2 := by sorry

end RoughSurfaceScattering
