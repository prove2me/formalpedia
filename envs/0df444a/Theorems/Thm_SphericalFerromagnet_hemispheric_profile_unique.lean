-- Prove2me | Theorems.Thm_SphericalFerromagnet_hemispheric_profile_unique
-- name    : SphericalFerromagnet.hemispheric_profile_unique
-- status  : Disproved
-- author  : @shivm
-- created : 2026-10-04T14:25:33.694704+00:00
-- url     : https://prove2.me/theorems/5416b643-056d-4f3f-9175-fa85fe5754cf
-- title:
--   Uniqueness of the hemispheric $H_{0,2}$ profile for $\kappa\ge 4$
-- statement:
--   **Conjecture (Gustafson–Meinert–Melcher, Remark 3.18; AIM problem 241).** For every $\kappa\ge4$ there is exactly one $H_{0,2}$ critical profile: a profile $h$, $C^\infty$ on $[0,\pi]$ and inducing a smooth map $S^2\to S^2$, solving
--   $$h''+\cot\theta\,h'-\frac{\sin 2h}{2\sin^2\theta}-\frac{\kappa}{2}\sin(2h-2\theta)=0\qquad(0<\theta<\pi)$$
--   with $h(0)=0$, $h(\pi)=2\pi$, $h(\pi-\theta)=2\pi-h(\theta)$.
--
--   Uniqueness means any two such profiles agree on $[0,\pi]$; profiles are functions on $\mathbb R$ whose values outside $[0,\pi]$ are unconstrained.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, Remark 3.18 (conjecture), eq. (2.6), Definition 3.1; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM, problems/241-spherical-ferromagnet-profile-uniqueness.md)

import Definitions.Def_spherical_ferromagnet_profile_defs

open scoped ContDiff

namespace SphericalFerromagnet

theorem hemispheric_profile_unique (κ : ℝ) (hκ : 4 ≤ κ) :
    ∃ h : ℝ → ℝ, IsH02CriticalProfile κ h ∧
      ∀ g : ℝ → ℝ, IsH02CriticalProfile κ g → ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, g θ = h θ := by sorry

end SphericalFerromagnet
