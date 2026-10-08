-- Prove2me | Theorems.Thm_SphericalFerromagnet_shoot_exists
-- name    : SphericalFerromagnet.shoot_exists
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T18:38:06.196423+00:00
-- url     : https://prove2.me/theorems/e0847c87-2abd-40f1-b0e5-3d0a77de2a9b
-- title:
--   Shooting solutions exist for slopes $a\in[3,5]$ at $\kappa=4$
-- statement:
--   For every $a\in[3,5]$ there is $h$ with $\mathrm{ShootSol}(a,h)$ and $\mathrm{PoleRep}(h)$:
--   $$\exists h:\ h\in C^\infty[0,\tfrac\pi2],\ h(0)=0,\ h'(0)=a,\ \text{(2.6) with }\kappa=4\text{ on }(0,\tfrac\pi2),\ \text{and } h \text{ is pole-regular.}$$
--
--   $\theta=0$ is a regular singular point (indicial roots $\pm1$); the slope $a$ selects the regular branch $h\sim a\theta$. Pole regularity ($\mathrm{PoleRep}$) means $\cos h$ and $\sin h/\sin\theta$ are smooth functions of $\cos\theta$ near $\theta=0$.
--
--   Validated-numerics input to the AIM 241 disproof, together with the three other shooting lemmas.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1; shooting at kappa=4 for AIM problem 241

import Definitions.Def_spherical_ferromagnet_shooting_defs

open scoped ContDiff
open Real Set

namespace SphericalFerromagnet

theorem shoot_exists (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 5) : ∃ h, ShootSol a h ∧ PoleRep h := by sorry

end SphericalFerromagnet
