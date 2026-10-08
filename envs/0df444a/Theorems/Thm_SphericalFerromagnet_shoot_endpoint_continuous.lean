-- Prove2me | Theorems.Thm_SphericalFerromagnet_shoot_endpoint_continuous
-- name    : SphericalFerromagnet.shoot_endpoint_continuous
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T18:38:08.525926+00:00
-- url     : https://prove2.me/theorems/52e8c10c-9682-4843-a836-67dbd1d5340c
-- title:
--   Shooting endpoint depends continuously on the slope at $\kappa=4$
-- statement:
--   There is $\Phi$, continuous on $[3,5]$, with
--   $$h(\pi/2)=\Phi(a)\quad\text{whenever } a\in[3,5] \text{ and } \mathrm{ShootSol}(a,h).$$
--
--   So the shot with slope $a$ is unique (at least its value at $\pi/2$), and its endpoint depends continuously on $a$. Uniqueness is not automatic: $\theta=0$ is a singular point of (2.6).
--
--   Here $\kappa=4$ in (2.6),
--   $$h''+\cot\theta\,h'-\frac{\sin 2h}{2\sin^2\theta}-\frac{\kappa}{2}\sin(2h-2\theta)=0\qquad(2.6)$$
--   and $h_a$ denotes a solution with $\mathrm{ShootSol}(a,h_a)$: $C^\infty$ on $[0,\pi/2]$, $h_a(0)=0$, $h_a'(0)=a$, solving (2.6) on $(0,\pi/2)$.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6); shooting at kappa=4 for AIM problem 241

import Definitions.Def_spherical_ferromagnet_shooting_defs

open scoped ContDiff
open Real Set

namespace SphericalFerromagnet

theorem shoot_endpoint_continuous :
    ∃ Φ : ℝ → ℝ, ContinuousOn Φ (Icc 3 5) ∧
      ∀ a ∈ Icc (3 : ℝ) 5, ∀ h, ShootSol a h → h (π / 2) = Φ a := by sorry

end SphericalFerromagnet
