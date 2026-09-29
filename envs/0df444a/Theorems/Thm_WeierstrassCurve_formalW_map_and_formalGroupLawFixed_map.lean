-- Prove2me | Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
-- name    : WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/6b72dfd4-0e1e-5f17-8728-7c6105fe3e22
-- title:
--   Base change of the Weierstrass formal group law
-- statement:
--   Let $R$ and $S$ be commutative rings, let $W$ be a Weierstrass curve over $R$, and let $f : R \to S$ be a ring homomorphism; write $W.\mathrm{map}\,f$ for the Weierstrass curve over $S$ obtained by applying $f$ to the coefficients $a_1,a_2,a_3,a_4,a_6$. The theorem asserts two equalities simultaneously. First, `formalW` commutes with $f$: the one-variable series $\mathrm{formalW}$, whose $n$-th coefficient is by definition the $n$-th coefficient of the $n$-th iterate `wIter` of the substitution operator `wSubst` applied to $0$, satisfies $(W.\mathrm{map}\,f).\mathrm{formalW} = \mathrm{map}\,f\,(W.\mathrm{formalW})$, where $\mathrm{map}\,f$ acts coefficientwise on $R[\![X]\!]$. Second, the same holds for the two-variable series `formalGroupLawFixed`, defined as the substitution of $\mathrm{fgZ3Fixed} = -X_0 - X_1 + \mathrm{fgZ3NumFixed}\cdot(\mathrm{fgZ3Denom})^{-1}$ (the inverse taken via `invOfUnit` at the unit $1$) into the one-variable series $\mathrm{fgInv} = -X\cdot(\mathrm{fgInvDenom})^{-1}$: one has $(W.\mathrm{map}\,f).\mathrm{formalGroupLawFixed} = \mathrm{map}\,f\,(W.\mathrm{formalGroupLawFixed})$ in $S[\![X_0,X_1]\!]$, with $\mathrm{map}\,f$ again acting coefficientwise on multivariate power series indexed by $\mathrm{Fin}\,2$.
--
--   This is the compatibility of Silverman's formal group attached to a Weierstrass equation with base change of the coefficient ring: both the series $w(z)$ of the chart at the origin and the resulting formal group law are obtained from the $a_i$ by operations stable under coefficientwise ring maps. It allows formal-group identities established over a convenient base (for instance a polynomial ring or a domain) to be transported to arbitrary bases, and it is used throughout the construction of formal-group and Drinfeld-basis data on moduli of elliptic curves with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map.lean

import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open PowerSeries

theorem WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map
    {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    (W.map f).formalW = PowerSeries.map f W.formalW ∧
      (W.map f).formalGroupLawFixed = MvPowerSeries.map f W.formalGroupLawFixed := by sorry
