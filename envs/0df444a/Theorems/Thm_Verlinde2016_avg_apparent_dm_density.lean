-- Prove2me | Theorems.Thm_Verlinde2016_avg_apparent_dm_density
-- name    : Verlinde2016.avg_apparent_dm_density
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T22:53:42.821019+00:00
-- url     : https://prove2.me/theorems/3f569721-d170-4c20-aa50-064c467205db
-- title:
--   Eq. (7.47) — averaged apparent dark matter density $\bar\rho_D^2=(4-\beta_B)\,a_0\bar\rho_B/(8\pi G r)$
-- statement:
--   Let $G>0$, $a_0>0$. Let $M_B$ be a baryonic mass profile, positive and differentiable on $(0,\infty)$, and $M_D$ an apparent dark matter mass profile, continuous on $(0,\infty)$, satisfying the main formula (7.40)
--   $$\int_0^r\frac{G\,M_D(r')^2}{r'^2}\,dr' = \frac{M_B(r)\,a_0\,r}{6}\qquad (r>0).$$
--   With the averaged densities $\bar\rho_B,\bar\rho_D$ of (7.45) and the slope parameter $\beta_B = -\,d\log\bar\rho_B/d\log r$ of (7.46), for every $r>0$
--   $$\bar\rho_D(r)^2 = \big(4-\beta_B(r)\big)\,\frac{a_0\,\bar\rho_B(r)}{8\pi G\,r}.$$
--   (The paper says this follows "by differentiating (7.36)"; the computation is the differentiation of its spherically symmetric form (7.40).)
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 40, eqs. (7.45)-(7.47), using (7.40) on p. 38

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem avg_apparent_dm_density (G a₀ : ℝ) (hG : 0 < G) (ha₀ : 0 < a₀)
    (M_B M_D : ℝ → ℝ) (hM_B_diff : DifferentiableOn ℝ M_B (Set.Ioi 0))
    (hM_B_pos : ∀ r : ℝ, 0 < r → 0 < M_B r) (hM_D_cont : ContinuousOn M_D (Set.Ioi 0))
    (hmain : ∀ r : ℝ, 0 < r → ∫ s in (0 : ℝ)..r, G * M_D s ^ 2 / s ^ 2 = M_B r * a₀ * r / 6) :
    ∀ r : ℝ, 0 < r → avgDensity M_D r ^ 2
      = (4 - slopeParam (avgDensity M_B) r) * a₀ * avgDensity M_B r / (8 * π * G * r) := by sorry

end Verlinde2016
