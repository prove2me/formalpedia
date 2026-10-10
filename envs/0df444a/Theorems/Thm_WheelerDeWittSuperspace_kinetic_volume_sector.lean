-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_kinetic_volume_sector
-- name    : WheelerDeWittSuperspace.kinetic_volume_sector
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T22:17:41.032718+00:00
-- url     : https://prove2.me/theorems/3e7a2303-e265-4f18-9392-6a3bad36f19c
-- title:
--   Wheeler–DeWitt kinetic operator on the conformal sector
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}$ be $C^2$ and let the metric at site $x_0$ be positive definite. For the wavefunction $\Psi(h)=f\big(\sqrt{\det h(x_0)}\big)$ and $v=\sqrt{\det h(x_0)}$,
--   $$\sum_{a,b,c,d}G_{abcd}(h(x_0))\,\partial_{ab}(x_0)\,\partial_{cd}(x_0)\Psi=-\tfrac38\,\big(v\,f''(v)+7f'(v)\big),$$
--   where $\partial_{ab}(x_0)$ is the partial derivative with respect to the entry $h_{ab}(x_0)$, all nine entries being independent coordinates.
-- source:
--   C. Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009) 877-901, https://arxiv.org/abs/0812.0295, eqs. (5)-(7); B. S. DeWitt, Quantum Theory of Gravity I. The Canonical Theory, Phys. Rev. 160 (1967) 1113-1148, https://doi.org/10.1103/PhysRev.160.1113

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 4 (conformal sector): on wavefunctions of the local volume
`v = √det h(x₀)`, the kinetic term is the ordinary differential operator
`-(3/8)(v f'' + 7 f')`. -/
theorem kinetic_volume_sector {X : Type*} [Fintype X] [DecidableEq X] (x₀ : X)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (h : Config X) (hpos : (metricAt h x₀).PosDef) :
    kinetic (fun h' => f (volume (metricAt h' x₀))) h x₀ =
      -(3 / 8 : ℂ) * ((volume (metricAt h x₀) : ℂ) *
          iteratedDeriv 2 f (volume (metricAt h x₀)) +
        7 * deriv f (volume (metricAt h x₀))) := by sorry

end WheelerDeWittSuperspace
