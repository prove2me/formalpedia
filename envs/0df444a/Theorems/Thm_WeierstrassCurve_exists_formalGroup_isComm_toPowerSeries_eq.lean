-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq
-- name    : WeierstrassCurve.exists_formalGroup_isComm_toPowerSeries_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/e2eb64ba-e52e-5bbb-a00e-cb2f720ea7e3
-- title:
--   Existence of the commutative Weierstrass formal group law
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, that is, a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in R$; no hypothesis on the discriminant or on $R$ is imposed. The assertion is that there exists a one-dimensional formal group $F$ over $R$ — a power series in two variables indexed by `Fin 2` with vanishing constant coefficient, with coefficient $1$ on each of the two linear monomials, and satisfying the associativity identity for formal group laws — together with a proof that $F$ is commutative, i.e. that its underlying series is invariant under substituting the second variable for the first and the first for the second, whose underlying series is exactly $W$'s Weierstrass formal group law [`WeierstrassCurve.formalGroupLawFixed`](def/WeierstrassCurve_FormalGroupLaw.html#L638). The latter is defined as the substitution of the two-variable series $W.fgZ3Fixed = -X_0 - X_1 + W.fgZ3NumFixed \cdot \mathrm{invOfUnit}(W.fgZ3Denom, 1)$ into the single-variable series $W.fgInv = -X \cdot \mathrm{invOfUnit}(W.fgInvDenom, 1)$, the inverses being taken by the power-series inversion of series whose constant coefficient is the unit $1$.
--
--   This is the classical statement that the formal group law attached to a Weierstrass equation, built from the addition formulae in the parameter at the origin, satisfies the formal group axioms and is commutative, here over an arbitrary commutative ring and with no ellipticity assumption. It supplies the formal-group input to the local study of adic completions of the integral models of modular curves, for instance in the statements on domains, integral closedness and reducedness at full level and at $\Gamma_0$-type level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_formalGroup_isComm_toPowerSeries_eq
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    ∃ (F : FormalGroup R) (_ : F.IsComm), F.toPowerSeries = W.formalGroupLawFixed := by sorry
