-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_pow_of_variableChange
-- name    : WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_of_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/7e7b7615-d3a5-5418-aec4-98aad51cbd68
-- title:
--   Invariance of [q]=u X^q under Weierstrass variable change
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, $C$ a Weierstrass variable change over $R$, and $q$ a natural number. Let $F$ and $F'$ be formal group laws over $R$ whose underlying two-variable power series are the explicit Weierstrass laws of $W$ and of the transformed curve $C \bullet W$ respectively: $F$'s series equals `W.formalGroupLawFixed`, the result of substituting the two-variable series `W.fgZ3Fixed` $= -X_0 - X_1 + \mathtt{fgZ3NumFixed}\cdot\mathtt{invOfUnit fgZ3Denom}$ into the one-variable inversion series `W.fgInv` $= -X\cdot\mathtt{invOfUnit fgInvDenom}$, and $F'$'s series equals the same construction applied to $C \bullet W$. Here `nthSeries` is the multiplication-by-$n$ series of a formal group law, defined recursively by $[0] = 0$ and $[n+1] = F([n](X), X)$ (substitution of the pair $([n], X)$ into the law). The assertion is: if there is a unit $u \in R[\![X]\!]$ with $F.\mathrm{nthSeries}\,q = u\,X^q$, then there is a unit $u' \in R[\![X]\!]$ with $F'.\mathrm{nthSeries}\,q = u'\,X^q$. No hypothesis is imposed on $q$ or on $R$ beyond commutativity.
--
--   The property that the $[q]$-series of a Weierstrass formal group is $X^q$ times a unit — the condition controlling the height of the formal group in characteristic dividing $q$ — depends only on the curve up to change of Weierstrass coordinates, not on the chosen model. It is used where an ordinarity-type hypothesis is available for one Weierstrass model while the formal group of another, isomorphic, model is the one actually analysed, and is cited in the construction of the power-series algebra isomorphisms attached to level structures on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_pow_of_variableChange.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_of_variableChange
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (q : ℕ)
    (F F' : FormalGroup R) (hF : F.toPowerSeries = W.formalGroupLawFixed)
    (hF' : F'.toPowerSeries = (C • W).formalGroupLawFixed)
    (h : ∃ u : PowerSeries R, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q) :
    ∃ u : PowerSeries R, IsUnit u ∧ F'.nthSeries q = u * PowerSeries.X ^ q := by sorry
