-- Prove2me | Theorems.Thm_SphericalFerromagnet_shoot_three_overshoots
-- name    : SphericalFerromagnet.shoot_three_overshoots
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T18:38:16.931098+00:00
-- url     : https://prove2.me/theorems/9a4bc0e7-e614-40ab-821a-3b8c83017df0
-- title:
--   Slope-3 shot overshoots: $h_3(\pi/2)>\pi$ at $\kappa=4$
-- statement:
--   Every shot with slope $3$ ends above $\pi$ at the equator:
--   $$\mathrm{ShootSol}(3,h)\implies h(\pi/2)>\pi.$$
--
--   Here $\kappa=4$ in (2.6),
--   $$h''+\cot\theta\,h'-\frac{\sin 2h}{2\sin^2\theta}-\frac{\kappa}{2}\sin(2h-2\theta)=0\qquad(2.6)$$
--   and $h_a$ denotes a solution with $\mathrm{ShootSol}(a,h_a)$: $C^\infty$ on $[0,\pi/2]$, $h_a(0)=0$, $h_a'(0)=a$, solving (2.6) on $(0,\pi/2)$.
--
--   This is a validated-numerics fact. Numerics (scipy `solve_ivp`, rtol $10^{-12}$, started at $\theta_0=10^{-6}$ from $h=a\theta_0$, $h'=a$, integrated to $\pi/2$) give $h_3(\pi/2)-\pi\approx+0.087$ and $h_5(\pi/2)-\pi\approx-0.129$.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Remark 3.18 (numerics); shooting at kappa=4 for AIM problem 241

import Definitions.Def_spherical_ferromagnet_shooting_defs

open scoped ContDiff
open Real Set

namespace SphericalFerromagnet

theorem shoot_three_overshoots : ∀ h, ShootSol 3 h → π < h (π / 2) := by sorry

end SphericalFerromagnet
