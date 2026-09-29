-- Prove2me | Theorems.Thm_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map
-- name    : WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/ecf6f079-abc0-5cab-9214-547d56aeb3c7
-- title:
--   Base change of the variable-change denominator and series
-- statement:
--   Let $R$ and $S$ be commutative rings, let $W$ be a Weierstrass curve over $R$ (given by its coefficients $a_1,a_2,a_3,a_4,a_6$), let $C$ be an admissible change of variables over $R$, i.e. a `WeierstrassCurve.VariableChange R` with data $u \in R^\times$ and $r,s,t \in R$, and let $f \colon R \to S$ be a ring homomorphism. Write $w_W \in R[[X]]$ for `W.formalW`, the power series whose $n$-th coefficient is the $n$-th coefficient of the $n$-th Weierstrass iterate `W.wIter n`, and set $$D_W(C) = 1 + s\,(X - r\,w_W) + t\,w_W, \qquad \psi_W(C) = u\,(X - r\,w_W)\cdot \mathrm{invOfUnit}(D_W(C),1),$$ the constants being inserted via `PowerSeries.C` and the inverse being `PowerSeries.invOfUnit` taken with respect to the unit $1$. The theorem asserts the conjunction of two identities in $S[[X]]$: first, that the denominator of the base-changed curve $W \otimes_f S$ at the base-changed change of variables $f_*C$ equals the image of $D_W(C)$ under the coefficientwise map $S[[X]] \ni \mathrm{map}\,f$, and second, that likewise $\psi_{W \otimes_f S}(f_*C) = \mathrm{map}\,f\,(\psi_W(C))$.
--
--   This is the base-change compatibility (functoriality in the coefficient ring) of the change-of-parameter series attached to an admissible change of variables on a Weierstrass cubic. It is used to transfer the universal-curve computation that $\psi_C$ is an isomorphism of formal group laws to arbitrary base rings, and is cited in the construction of isomorphisms of formal laws over adic completions and in the transport of level structures on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map.lean

import Definitions.Def_WeierstrassCurve_VariableChangeSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map
    {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
    (f : R →+* S) :
    (W.map f).variableChangeDenom (C.map f) = PowerSeries.map f (W.variableChangeDenom C) ∧
      (W.map f).variableChangeSeries (C.map f) = PowerSeries.map f (W.variableChangeSeries C) := by sorry
