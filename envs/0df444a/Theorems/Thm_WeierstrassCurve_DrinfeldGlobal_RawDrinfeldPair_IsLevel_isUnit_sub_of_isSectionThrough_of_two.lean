-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_sub_of_isSectionThrough_of_two
-- name    : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.isUnit_sub_of_isSectionThrough_of_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f2cc2a92-3327-5798-a866-2a3b8899879f
-- title:
--   Drinfeld Γ(2)-basis: x_P-x_Q is a unit
-- statement:
--   Let $A_0$ be a commutative ring and let $\mathcal{G}$ be a family of group laws over $A_0$, assigning to every $A_0$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant a relative group law on the projective model of $W$. Assume $\mathcal{G}$ is chord–tangent, i.e. for all such $T$, $W$ and units $\Delta$ there is a points-evaluation $ev$ satisfying `IsPointsEval`, and that $\mathcal{G}$ has the origin as identity, i.e. for all such data there is a ring homomorphism from the origin chart ring of $W$ to $T$ which is an origin-chart section of the identity section of $\mathcal{G}$ and sends both $x/y$ and $z/y$ to $0$. Let $\mathcal{T}$ be a level-$2$ transport for $\mathcal{G}$ (functorial maps of raw Drinfeld pairs along $A_0$-algebra homomorphisms and along Weierstrass variable changes, compatible with identities, composition and the level-$2$ condition), assumed to be a section transport: after the corresponding maps of projective models, the $P$- and $Q$-sections of the transported pair are the images of the original ones, for coefficient homomorphisms and for variable-change homomorphisms. Let $T$ be an $A_0$-algebra in which $2$ is a unit, let $E$ be a Weierstrass curve over $T$, and let $x$ be a raw Drinfeld pair over $T$, i.e. a projective Weierstrass curve $x.\mathrm{curve}$ together with two sections $x.P$, $x.Q$. Assume $x$ is of level $2$ for $\mathcal{G}$ over the projective model of $E$: $x.\mathrm{curve}$ equals that model, its discriminant is a unit, and $x.P, x.Q$ form a Drinfeld basis of order $2$ for the associated group law, in the sense that their basis divisor equals the $2$-torsion ideal. Finally let $x_P,y_P,x_Q,y_Q \in T$ be such that $x.P$ passes through $(x_P,y_P)$ and $x.Q$ through $(x_Q,y_Q)$, meaning that there is a ring homomorphism from the $Z$-chart ring of $x.\mathrm{curve}$ to $T$ which is a $Z$-chart section of the given section with affine coordinates the indicated pair. Then $x_P - x_Q$ is a unit in $T$.
--
--   This is the level-$2$ form, over an arbitrary base ring in which $2$ is invertible, of the independence property of a Drinfeld basis: the two basis points are distinct in every fibre, and since a point of order $2$ is determined by its $x$-coordinate once $2$ is invertible, the difference of the two $x$-coordinates is even invertible. It feeds the lifting theorem for level structures along surjections with nilpotent kernel and the count of level-$2$ Drinfeld structures over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_sub_of_isSectionThrough_of_two.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.isUnit_sub_of_isSectionThrough_of_two
    (A₀ : Type) [CommRing A₀] (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 2) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (h2T : IsUnit ((2 : ℕ) : T))
    (x : RawDrinfeldPair T) (hx : RawDrinfeldPair.IsLevel 𝒢 2 E x)
    (xP yP xQ yQ : T) (hP : IsSectionThrough x.P xP yP) (hQ : IsSectionThrough x.Q xQ yQ) :
    IsUnit (xP - xQ) := by sorry
