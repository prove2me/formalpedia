-- Prove2me | Theorems.Thm_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed
-- name    : WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/708e7732-ad07-5624-8330-f34fc51d906b
-- title:
--   Invariant differential of the Weierstrass formal group
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with coefficients $a_1,\dots,a_6$. Write $w =$ `W.formalW` for the one-variable power series in $R[[X]]$ whose $n$-th coefficient is the $n$-th coefficient of the $n$-th iterate `W.wIter n`, the iterates being defined by `wIter 0 = 0` and `wIter (k+1) = W.wSubst (wIter k)`; and write $F =$ `W.formalGroupLawFixed` for the two-variable series obtained by substituting $$-X_0 - X_1 + \bigl(\mathrm{W.fgZ3NumFixed}\bigr)\cdot\mathrm{invOfUnit}(\mathrm{W.fgZ3Denom},1)$$ into the one-variable series $-X\cdot\mathrm{invOfUnit}(\mathrm{W.fgInvDenom},1)$. Let `pderivLin 0` be the $R$-linear operator on $R[[X_0,X_1]]$ sending a series to the one whose coefficient at a multidegree $d$ is $(d_0+1)$ times the coefficient at $d + \delta_0$, i.e. the formal partial derivative in $X_0$. The assertion is the identity in $R[[X]]$
--   $$w\,\bigl(a_3 w + a_1 X - 2\bigr) \;=\; \bigl(w - X\,w'\bigr)\cdot \bigl(\partial_{X_0} F\bigr)\bigl|_{X_0 = 0,\;X_1 = X},$$
--   where $w'$ is the formal derivative of $w$ and the right-hand substitution is `MvPowerSeries.subst ![0, X]`.
--
--   This is the power-series form of the invariance of the Weierstrass differential $\omega = dx/(2y + a_1x + a_3)$ under the formal group law: it identifies $\partial_{X_0}F(0,T)$, the reciprocal of the normalised invariant differential, with $w(a_3w + a_1T - 2)/(w - Tw')$ in the $(z,w)$-chart. It is used by [`WeierstrassCurve.ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame`](thm.html#WeierstrassCurve.ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame) to compare the invariant differential of the formal group with the differential on the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.formalW * (PowerSeries.C W.a₃ * W.formalW + PowerSeries.C W.a₁ * PowerSeries.X - 2)) = (W.formalW - PowerSeries.X * PowerSeries.derivative R W.formalW) * MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X]
        (MvPowerSeries.pderivLin 0 W.formalGroupLawFixed) := by sorry
