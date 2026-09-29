-- Prove2me | Theorems.Thm_WeierstrassCurve_nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
-- name    : WeierstrassCurve.nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6fe797dd-5e32-5050-a2e0-0ab01e1bf2d3
-- title:
--   Multiplication by q in characteristic q has order at most q²
-- statement:
--   Fix a natural number $q$ which is prime, a field $k$ (in the lowest universe) of characteristic $q$, and a Weierstrass curve $W$ over $k$ satisfying `W.IsElliptic`. Let $F$ be a formal group law over $k$ whose underlying power series in two variables, `F.toPowerSeries`, is equal to `W.formalGroupLawFixed`, the Weierstrass formal group law of $W$ obtained by substituting the series $W.\mathrm{fgZ3Fixed} = -X_0 - X_1 + W.\mathrm{fgZ3NumFixed}\cdot(W.\mathrm{fgZ3Denom})^{-1}$ into the one-variable series $W.\mathrm{fgInv} = -X\cdot(W.\mathrm{fgInvDenom})^{-1}$ (the inverses being formed by `MvPowerSeries.invOfUnit`/`PowerSeries.invOfUnit` at the unit $1$). The conclusion concerns the multiplication-by-$n$ series of $F$, defined recursively by `F.nthSeries 0 = 0` and `F.nthSeries (n+1) =` the substitution of the pair $(\mathrm{nthSeries}\ n, X)$ into `F.toPowerSeries`, i.e. $[n+1](Z) = F([n](Z), Z)$. The assertion is the conjunction of two facts about the single series $[q](Z) =$ `F.nthSeries q`: first, that it is not the zero power series; second, that $X^{q\cdot q + 1}$ does not divide it. Equivalently, $[q]_F \neq 0$ and its order of vanishing at the origin is at most $q^2$.
--
--   This is the formal-group shadow of the classical fact that multiplication by $q$ on an elliptic curve in characteristic $q$ is an isogeny of degree $q^2$, read off in the parameter at the origin: the completed kernel is $\operatorname{Spec} k[[Z]]/([q]_F)$, of rank at most $q^2$. It is the input used in [`WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul`](thm.html#WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul), and through it to the bound height $\le 2$ for the formal group of an elliptic curve; the proof works with the division polynomials $W.\psi$, $W.\Phi$, $W.\Psi^{\mathrm{Sq}}$ and with the generic point of $W$ over the formal group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nthSeries_ne_zero_and_not_X_pow_dvd_of_charP.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed) :
    F.nthSeries q ≠ 0 ∧ ¬ (PowerSeries.X ^ (q * q + 1) ∣ F.nthSeries q) := by sorry
