-- Prove2me | Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries
-- name    : WeierstrassCurve.coeff_one_variableChangeSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e8e8a224-c760-56b1-9b28-99ccf71be277
-- title:
--   Linear coefficient of the change-of-parameter series is u
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve over $R$ and let $C$ be an admissible change of variables over $R$, with components $u$ (a unit of $R$) and $r,s,t\in R$. Write $w_W =$ `W.formalW` for the power series whose $n$-th coefficient is the $n$-th coefficient of the $n$-th iterate `W.wIter n`, and set $\delta_C = 1 + s\,(X - r\,w_W) + t\,w_W$, the series `W.variableChangeDenom C`. The series `W.variableChangeSeries C` is by definition $u\,(X - r\,w_W)\cdot \delta_C^{-1}$, where the inverse is the formal inverse `PowerSeries.invOfUnit` of $\delta_C$ formed with respect to the unit $1$ as the prescribed value of the constant coefficient. The assertion is that the coefficient of $X^1$ in this series equals $u$ (more precisely, the image of the unit $u$ in $R$).
--
--   This is the linear-term computation for the substitution that relates the formal parameters attached to two Weierstrass models differing by the admissible change $(u,r,s,t)$: the change-of-parameter series has the shape $u\,z + O(z^2)$, so it is invertible as a formal substitution. It is one conjunct of the statement that this series gives an isomorphism of the associated formal group laws, and is used in the study of the action of such changes on the parameter at the origin in the level structures for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_coeff_one_variableChangeSeries.lean

import Definitions.Def_WeierstrassCurve_VariableChangeSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.coeff_one_variableChangeSeries
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    PowerSeries.coeff 1 (W.variableChangeSeries C) = (C.u : R) := by sorry
