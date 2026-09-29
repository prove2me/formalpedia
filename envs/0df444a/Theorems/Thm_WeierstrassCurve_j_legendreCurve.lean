-- Prove2me | Theorems.Thm_WeierstrassCurve_j_legendreCurve
-- name    : WeierstrassCurve.j_legendreCurve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/70e578aa-40b6-5f86-a41e-69272b6f6d09
-- title:
--   The j-invariant of the Legendre curve
-- statement:
--   Let $K$ be a field and $t \in K$. Write $E_t$ for the Weierstrass curve over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0, -(1+t), 0, t, 0)$, i.e. the model $y^2 = x^3 - (1+t)x^2 + tx = x(x-1)(x-t)$; this is the curve `legendreCurve t`. Assume that $E_t$ is elliptic in the sense of Mathlib's `IsElliptic`, that is, its discriminant $\Delta(E_t)$ is a unit of $K$, so that the $j$-invariant $j(E_t) = \Delta(E_t)^{-1} c_4(E_t)^3$ is defined. The assertion is then the identity
--   $$j(E_t) = \frac{2^8\,(t^2 - t + 1)^3}{t^2\,(t-1)^2},$$
--   the right-hand side being the quantity [`ModularCurve.legendreJ t`](def/ModularCurve_LegendreJ.html#L7) defined by exactly that formula (a division in the field $K$). Note that no hypotheses $2 \neq 0$, $t \neq 0$, $t \neq 1$ are imposed: they are consequences of $\Delta(E_t)$ being a unit, since $\Delta(E_t) = 16\,t^2(t-1)^2$.
--
--   This is the classical formula for the $j$-invariant of the Legendre family $y^2 = x(x-1)(x-\lambda)$. It is used to pass between Legendre parameters and $j$-invariants, for instance in the identification of the set of supersingular $j$-invariants in characteristic $p$ with the image under [`ModularCurve.legendreJ`](def/ModularCurve_LegendreJ.html#L7) of the corresponding set of parameters, and in the accompanying identities for the Deuring polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_j_legendreCurve.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_LegendreJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.j_legendreCurve {K : Type*} [Field K] (t : K) [(legendreCurve t).IsElliptic] :
    (legendreCurve t).j = ModularCurve.legendreJ t := by sorry
