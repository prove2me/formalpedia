-- Prove2me | Theorems.Thm_Verlinde2016_density_parameter_relation
-- name    : Verlinde2016.density_parameter_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T23:45:53.490806+00:00
-- url     : https://prove2.me/theorems/b4992f31-c28b-430f-9a81-6413584d662e
-- title:
--   Eq. (7.51) — $\Omega_D^2=\frac43\Omega_B$ from (7.47) at the Hubble radius
-- statement:
--   Apply (7.47) to the whole universe with constant baryonic density ($\beta_B=0$) at the Hubble radius $r=L=c/H_0$, with $a_0=cH_0$:
--   $$\bar\rho_D^2 = 4\,\frac{a_0\,\bar\rho_B}{8\pi G\,L}.$$
--   With the critical density $\rho_{\rm crit} = \dfrac{3H_0^2}{8\pi G} = \dfrac{3a_0}{8\pi G}\dfrac1L$ (7.50) and $\Omega_B=\bar\rho_B/\rho_{\rm crit}$, $\Omega_D=\bar\rho_D/\rho_{\rm crit}$, this gives
--   $$\Omega_D^2 = \frac43\,\Omega_B .$$
--   The specialized form of (7.47) is taken as the hypothesis.
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 41, eqs. (7.50)-(7.51), using (7.47) p. 40

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem density_parameter_relation (G c H₀ ρ_B ρ_D : ℝ) (hG : 0 < G) (hc : 0 < c) (hH₀ : 0 < H₀)
    (h747 : ρ_D ^ 2 = (4 - 0) * (c * H₀) * ρ_B / (8 * π * G * (c / H₀))) :
    (ρ_D / (3 * H₀ ^ 2 / (8 * π * G))) ^ 2 = 4 / 3 * (ρ_B / (3 * H₀ ^ 2 / (8 * π * G))) := by sorry

end Verlinde2016
