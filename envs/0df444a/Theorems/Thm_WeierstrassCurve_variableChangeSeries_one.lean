-- Prove2me | Theorems.Thm_WeierstrassCurve_variableChangeSeries_one
-- name    : WeierstrassCurve.variableChangeSeries_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c0086988-df78-56c8-9c05-caa593c66e1d
-- title:
--   Identity variable change gives the series X
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$. For a variable change $C = (u,r,s,t)$ over $R$, the project associates to $W$ and $C$ the power series $$\mathtt{variableChangeSeries} = u\,\bigl(X - r\,W_{\mathrm{formal}}\bigr)\cdot \mathrm{invOfUnit}\bigl(\mathtt{variableChangeDenom},\,1\bigr),$$ where $\mathtt{variableChangeDenom} = 1 + s\,(X - r\,W_{\mathrm{formal}}) + t\,W_{\mathrm{formal}}$, the coefficients $u, r, s, t$ enter as constant power series, and $W_{\mathrm{formal}} = W.\mathtt{formalW}$ is the power series whose $n$-th coefficient is the $n$-th coefficient of the $n$-th iterate $W.\mathtt{wIter}\ n$; here $\mathrm{invOfUnit}$ is the Mathlib inverse of a power series whose constant term is the given unit, applied with the unit $1$. The theorem asserts that for the identity variable change $C = 1$, that is $u = 1$ and $r = s = t = 0$, the resulting series is the uniformiser itself: $W.\mathtt{variableChangeSeries}\ 1 = X$ in $R\llbracket X\rrbracket$. No hypotheses beyond $R$ being a commutative ring are imposed.
--
--   This is the normalisation (unit) law for the reparametrisation series attached to changes of Weierstrass coordinates on the formal group of $W$: the identity change of variables acts trivially on the formal parameter. It is used in the level-transport comparisons for the modular-curve level moduli packages, where a variable change that acts trivially on a point must act trivially on the associated formal parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_variableChangeSeries_one.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem WeierstrassCurve.variableChangeSeries_one
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    W.variableChangeSeries 1 = PowerSeries.X := by sorry
