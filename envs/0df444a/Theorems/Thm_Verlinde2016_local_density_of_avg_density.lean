-- Prove2me | Theorems.Thm_Verlinde2016_local_density_of_avg_density
-- name    : Verlinde2016.local_density_of_avg_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:24:48.13173+00:00
-- url     : https://prove2.me/theorems/352e1fce-7b53-4c83-b4ad-dc5f7f517f40
-- title:
--   Eq. (7.48) — local density from averaged density, $\rho=(1-\beta/3)\bar\rho$
-- statement:
--   Let $\rho$ be a mass density profile, continuous on $(0,\infty)$ with $\rho(r')\,4\pi r'^2$ integrable on every $[0,r]$, and let $M(r) = \int_0^r\rho(r')\,4\pi r'^2\,dr'$ (7.39) be the enclosed mass, assumed positive for $r>0$. With the averaged density $\bar\rho$ of (7.45) and its slope parameter $\beta = -\,d\log\bar\rho/d\log r$ (7.46), for every $r>0$
--   $$\rho(r) = \Big(1-\frac13\beta(r)\Big)\,\bar\rho(r).$$
--   The paper states this for the apparent dark matter ($\rho=\rho_D$, $M=M_D$); the relation is kinematic and holds for any such profile, which is what is formalized.
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 40, eq. (7.48), with (7.39) p. 38 and (7.45)-(7.46) p. 40

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem local_density_of_avg_density (M ρ : ℝ → ℝ) (hρ_cont : ContinuousOn ρ (Set.Ioi 0))
    (hρ_int : ∀ r : ℝ, 0 < r →
      IntervalIntegrable (fun s => ρ s * (4 * π * s ^ 2)) MeasureTheory.volume 0 r)
    (hM : ∀ r : ℝ, 0 < r → M r = ∫ s in (0 : ℝ)..r, ρ s * (4 * π * s ^ 2))
    (hM_pos : ∀ r : ℝ, 0 < r → 0 < M r) :
    ∀ r : ℝ, 0 < r → ρ r = (1 - slopeParam (avgDensity M) r / 3) * avgDensity M r := by sorry

end Verlinde2016
