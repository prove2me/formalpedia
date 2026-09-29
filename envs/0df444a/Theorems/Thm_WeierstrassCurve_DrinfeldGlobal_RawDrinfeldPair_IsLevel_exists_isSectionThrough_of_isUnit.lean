-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
-- name    : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/05273cea-f8c3-51dd-b35c-128736516b0c
-- title:
--   Drinfeld basis sections factor through the affine chart
-- statement:
--   Fix a prime $q$, a commutative ring $A_0$, and a family $\mathcal{G}$ assigning to every $A_0$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with $\Delta_W$ a unit a relative group law on the projective model of $W$. Assume $\mathcal{G}$ is chord–tangent, i.e. each such group law admits a points-evaluation $\mathrm{ev}$ satisfying `IsPointsEval`, and has origin identity, i.e. for each such $W$ there is a ring homomorphism $\chi$ from the origin-chart ring to $T$ realising the unit section as a section of that chart and sending $x/y$ and $z/y$ to $0$. Let $\mathcal{T}$ be a transport datum for $\mathcal{G}$ at level $q$ (base change along $A_0$-algebra maps and Weierstrass variable changes, functorially, preserving the level condition), assumed to satisfy `IsSectionTransport`: the two marked sections of the transported pair pull back, along $\mathrm{Proj}$ of any variable-change hom, respectively coefficient hom, to the original ones. Let $T$ be an $A_0$-algebra, $E$ a Weierstrass curve over $T$ with $q$ invertible in $T$, and $x$ a raw Drinfeld pair over $T$ (a projective Weierstrass curve $x.\mathrm{curve}$ together with two sections $x.P$, $x.Q$) with $x.\mathrm{curve} = E$ and $\Delta$ a unit such that $x.P$, $x.Q$ form a Drinfeld basis for $\mathcal{G}$ at $q$, in the sense that the basis divisor equals the $q$-torsion ideal. Then there are $x_P, y_P \in T$ and $x_Q, y_Q \in T$ with $x.P$ a section through $(x_P, y_P)$ and $x.Q$ a section through $(x_Q, y_Q)$, i.e. each factors through the chart $z \neq 0$ with those affine coordinates.
--
--   This is the statement that, over a base in which $q$ is invertible, neither member of a Drinfeld $\Gamma(q)$-basis is the zero section, so that both lie in the finite chart and have affine coordinates in the base ring; it is the form of Katz–Mazur's non-vanishing of basis points used in this development. It feeds the analysis of diamond operators and of relabellings of full-level structures, where the members must be manipulated through their affine coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal IsLocalRing
open WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit
    (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (hq : IsUnit ((q : ℕ) : T))
    (x : RawDrinfeldPair T) (hx : RawDrinfeldPair.IsLevel 𝒢 q E x) :
    (∃ xP yP : T, IsSectionThrough x.P xP yP) ∧ (∃ xQ yQ : T, IsSectionThrough x.Q xQ yQ) := by sorry
