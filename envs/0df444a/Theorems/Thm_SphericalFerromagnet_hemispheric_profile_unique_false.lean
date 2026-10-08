-- Prove2me | Theorems.Thm_SphericalFerromagnet_hemispheric_profile_unique_false
-- name    : SphericalFerromagnet.hemispheric_profile_unique_false
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-04T18:18:10.640746+00:00
-- url     : https://prove2.me/theorems/287a9372-231b-44ee-a04d-abb6c0004e75
-- title:
--   Uniqueness of the hemispheric $H_{0,2}$ profile fails at $\kappa=4$
-- statement:
--   The conjectured uniqueness (Remark 3.18) is false:
--   $$\neg\Bigl(\forall\kappa\ge4\ \exists h\in\mathcal H(\kappa)\ \forall g\in\mathcal H(\kappa)\ \forall\theta\in[0,\pi]:\ g(\theta)=h(\theta)\Bigr),$$
--   where $\mathcal H(\kappa)$ is the set of $H_{0,2}$ critical profiles for $\kappa$ (smooth on $[0,\pi]$, inducing a smooth map $S^2\to S^2$, solving (2.6), $h(0)=0$, $h(\pi)=2\pi$, $h(\pi-\theta)=2\pi-h(\theta)$).
--
--   This is the disproof target of the AIM 241 mission: it is exactly the negation of `SphericalFerromagnet.hemispheric_profile_unique`. Once it is proved, its proof can be inlined into a self-contained disproof of that goal.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, Remark 3.18 (conjecture), eq. (2.6), Definition 3.1; AIM open problems list, problem 241

import Definitions.Def_spherical_ferromagnet_profile_defs

open scoped ContDiff

namespace SphericalFerromagnet

theorem hemispheric_profile_unique_false :
    ¬ (∀ κ : ℝ, 4 ≤ κ → ∃ h : ℝ → ℝ, IsH02CriticalProfile κ h ∧
      ∀ g : ℝ → ℝ, IsH02CriticalProfile κ g → ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, g θ = h θ) := by sorry

end SphericalFerromagnet
