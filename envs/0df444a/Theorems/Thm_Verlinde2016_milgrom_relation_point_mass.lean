-- Prove2me | Theorems.Thm_Verlinde2016_milgrom_relation_point_mass
-- name    : Verlinde2016.milgrom_relation_point_mass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:03:49.377989+00:00
-- url     : https://prove2.me/theorems/afe6eb02-8774-4077-ba8b-00ca805745de
-- title:
--   Eq. (7.43) — Milgrom relation $g_D=\sqrt{a_M g_B}$, $a_M=a_0/6$, for a central point mass
-- statement:
--   Let $G>0$, $a_0>0$ and a constant baryonic mass $M_B>0$ concentrated at the origin. Let $M_D:(0,\infty)\to[0,\infty)$ be a continuous apparent dark matter mass profile satisfying Verlinde's main formula (7.40),
--   $$\int_0^r \frac{G\,M_D(r')^2}{r'^2}\,dr' = \frac{M_B\,a_0\,r}{6}\qquad\text{for all } r>0.$$
--   Then for all $r>0$,
--   $$g_D(r) = \sqrt{a_M\,g_B(r)},\qquad g_B(r) = \frac{GM_B}{r^2},\quad g_D(r)=\frac{GM_D(r)}{r^2},\quad a_M = \frac{a_0}{6}.$$
--   Continuity and non-negativity of $M_D$ on $(0,\infty)$ are the physical conventions of the paper (a mass enclosed in a radius), made explicit.
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 38, eqs. (7.40), (7.42), (7.43)

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem milgrom_relation_point_mass (G a₀ M_B : ℝ) (hG : 0 < G) (ha₀ : 0 < a₀) (hM_B : 0 < M_B)
    (M_D : ℝ → ℝ) (hM_D_cont : ContinuousOn M_D (Set.Ioi 0))
    (hM_D_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ M_D r)
    (hmain : ∀ r : ℝ, 0 < r → ∫ s in (0 : ℝ)..r, G * M_D s ^ 2 / s ^ 2 = M_B * a₀ * r / 6) :
    ∀ r : ℝ, 0 < r → G * M_D r / r ^ 2 = Real.sqrt (a₀ / 6 * (G * M_B / r ^ 2)) := by sorry

end Verlinde2016
