-- Prove2me | Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
-- name    : WeierstrassCurve.formalGroupLawFixed_comm_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/8836a5ce-1f1d-5ba3-affd-900e9b3a4c13
-- title:
--   Commutativity of the Weierstrass formal group law
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, given by its coefficients $a_1,a_2,a_3,a_4,a_6$. Consider the two-variable power series $F_W \in R[[X_0,X_1]]$, indexed by `Fin 2`, obtained as `W.formalGroupLawFixed`: it is the substitution into the one-variable series $\mathrm{fgInv}_W = -X \cdot \mathrm{invOfUnit}(\mathrm{fgInvDenom}_W, 1)$ of the two-variable series $\mathrm{fgZ3Fixed}_W = -X_0 - X_1 + \mathrm{fgZ3NumFixed}_W \cdot \mathrm{invOfUnit}(\mathrm{fgZ3Denom}_W, 1)$, where the auxiliary series $\mathrm{fgInvDenom}_W$, $\mathrm{fgZ3NumFixed}_W$ and $\mathrm{fgZ3Denom}_W$ are the data of the chord-and-tangent construction attached to $W$ and the inverses are taken by `invOfUnit` against the unit $1$. The assertion is that $F_W$ is invariant under interchanging the two variables: $F_W$ equals the result of substituting the pair $(X_1, X_0)$ into $F_W$, i.e. $F_W(X_0,X_1) = F_W(X_1,X_0)$. No hypothesis is imposed on $R$ beyond being a commutative ring; in particular $R$ need not be a domain and the discriminant of $W$ need not be a unit.
--
--   This is the commutativity of the formal group law of a Weierstrass curve, classically part of the statement that the formal group of an elliptic curve is a commutative one-parameter formal group law defined over $\mathbb{Z}[a_1,\dots,a_6]$. Removing the ellipticity and domain hypotheses makes the law usable over arbitrary base rings, and the result is invoked in the formal-group input to the moduli-theoretic constructions for modular curves (Drinfeld level structures and the associated $q$-expansion computations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing.lean

import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.formalGroupLawFixed_comm_of_commRing
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] W.formalGroupLawFixed := by sorry
