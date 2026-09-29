-- Prove2me | Theorems.Thm_WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom
-- name    : WeierstrassCurve.subst_fgInv_formalW_mul_fgInvDenom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/f377ddd2-4897-5da3-8a99-55de51e1b001
-- title:
--   Formal branch at the inverse point: w(i(T))(1-a₁T-a₃w)= -w
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$, with coefficients $a_1,a_2,a_3,a_4,a_6$. Three power series attached to $W$ enter. First, `W.formalW` $\in R[[X]]$, the formal branch, whose $n$-th coefficient is the $n$-th coefficient of the $n$-fold iterate `W.wIter n` of the substitution operator `W.wSubst` started at $0$; it has zero constant term and satisfies the Weierstrass chart equation $w = X^3 + a_1Xw + a_2X^2w + a_3w^2 + a_4Xw^2 + a_6w^3$. Second, `W.fgInvDenom` $= 1 - a_1X - a_3\,$`W.formalW`, a series with constant coefficient $1$. Third, `W.fgInv` $= -X \cdot$ `PowerSeries.invOfUnit W.fgInvDenom 1`, that is $-X$ times the multiplicative inverse of `W.fgInvDenom` (formed relative to the unit $1$ of $R$ matching its constant coefficient); thus `W.fgInv` is the formal series $-X/(1-a_1X-a_3w)$, which has zero constant term. The assertion is the identity in $R[[X]]$ $$\mathrm{subst}\,(\,\mathrm{W.fgInv}\,)\,(\,\mathrm{W.formalW}\,)\cdot \mathrm{W.fgInvDenom} = -\,\mathrm{W.formalW},$$ i.e. the branch evaluated at the formal inverse parameter, multiplied by $1-a_1X-a_3w$, equals $-w$.
--
--   This is the $(z,w)$-chart form of the inversion law $-(x,y) = (x,\,-y-a_1x-a_3)$ on a Weierstrass curve, expressed for the formal branch $w(z)$ and the formal inverse series $i(z) = -z/(1-a_1z-a_3w(z))$. It feeds into [`WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed`](thm.html#WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed), in the development of the invariant differential of the formal group of $W$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom.lean

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

theorem WeierstrassCurve.subst_fgInv_formalW_mul_fgInvDenom
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    PowerSeries.subst W.fgInv W.formalW * W.fgInvDenom = -W.formalW := by sorry
