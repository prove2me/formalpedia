-- Prove2me | Theorems.Thm_WeierstrassCurve_subst_zero_X_fgSlope
-- name    : WeierstrassCurve.subst_zero_X_fgSlope
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/e6eeac96-19d9-5264-82d3-abe7ec24b9af
-- title:
--   The slope series at X₀ = 0 is w(T)/T
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$. Recall the two-variable series `W.fgSlope` in `MvPowerSeries (Fin 2) R`, defined coefficientwise by assigning to the multidegree $d \colon \mathrm{Fin}\ 2 \to_{0} \mathbb{N}$ the coefficient of index $d\,0 + d\,1 + 1$ of the one-variable series `W.formalW`, where `W.formalW` is the power series whose $n$-th coefficient is the $n$-th coefficient of the $n$-fold iterate `W.wIter n` of the substitution operator `W.wSubst` started at $0$. The assertion is that substituting into `W.fgSlope`, by `MvPowerSeries.subst`, the family of one-variable power series sending the index $0$ to $0$ and the index $1$ to `PowerSeries.X`, yields the one-variable power series over $R$ whose $n$-th coefficient is the coefficient of index $n+1$ of `W.formalW`. Writing $w(T) = \sum_{n} w_n T^n$ for `W.formalW`, this says that the slope series evaluated at $(0, T)$ equals $\sum_{n \ge 0} w_{n+1} T^n$, the quotient $w(T)/T$.
--
--   Here `W.fgSlope` plays the role of the divided difference $(w(X_1) - w(X_0))/(X_1 - X_0)$ attached to the formal branch $w$ of a Weierstrass curve near the origin, and this is the specialisation of that slope at $X_0 = 0$. It is used in the verification of the functional identity satisfied by `W.formalW` and the formal group law, namely [`WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed`](thm.html#WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_subst_zero_X_fgSlope.lean

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

theorem WeierstrassCurve.subst_zero_X_fgSlope
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] W.fgSlope
      = PowerSeries.mk fun n => PowerSeries.coeff (n + 1) W.formalW := by sorry
