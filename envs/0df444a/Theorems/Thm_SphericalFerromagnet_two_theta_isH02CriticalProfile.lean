-- Prove2me | Theorems.Thm_SphericalFerromagnet_two_theta_isH02CriticalProfile
-- name    : SphericalFerromagnet.two_theta_isH02CriticalProfile
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T18:18:09.452543+00:00
-- url     : https://prove2.me/theorems/07d811ae-51af-40aa-8f01-2ca68e0c871c
-- title:
--   $h(\theta)=2\theta$ is an $H_{0,2}$ critical profile at $\kappa=4$
-- statement:
--   At $\kappa=4$ the profile
--   $$h(\theta)=2\theta$$
--   is an $H_{0,2}$ critical profile: $C^\infty$ on $[0,\pi]$, it induces a smooth map $S^2\to S^2$, solves (2.6) on $(0,\pi)$, and satisfies $h(0)=0$, $h(\pi)=2\pi$, $h(\pi-\theta)=2\pi-h(\theta)$.
--
--   It is one of the two distinct profiles used to disprove uniqueness at $\kappa=4$ (AIM problem 241).
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18

import Definitions.Def_spherical_ferromagnet_profile_defs

open scoped ContDiff

namespace SphericalFerromagnet

theorem two_theta_isH02CriticalProfile : IsH02CriticalProfile 4 (fun θ => 2 * θ) := by sorry

end SphericalFerromagnet
