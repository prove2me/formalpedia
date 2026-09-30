-- Prove2me | Theorems.Thm_Verlinde2016_inclusion_strain_sq_integral
-- name    : Verlinde2016.inclusion_strain_sq_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T22:26:08.423988+00:00
-- url     : https://prove2.me/theorems/139ce68e-ce41-48a2-995a-f4bcd3ab0d1a
-- title:
--   Eq. (4.44) — integral of the squared strain outside a spherical inclusion
-- statement:
--   Outside a ball $B_0$ of volume $NV_0$ the normal strain is $\varepsilon = NV_0/V$ (4.41), where $V$ is the volume enclosed at radius $r$. Writing $c = NV_0>0$, the integral of $\varepsilon^2$ over the complement of $B_0$, expressed in the volume variable $dV = A(r)\,dr$, equals the volume of $B_0$:
--   $$\int_{c}^{\infty}\left(\frac{c}{V}\right)^2 dV = c.$$
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 24, eq. (4.44)

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem inclusion_strain_sq_integral (c : ℝ) (hc : 0 < c) :
    ∫ V in Set.Ioi c, (c / V) ^ 2 = c := by sorry

end Verlinde2016
