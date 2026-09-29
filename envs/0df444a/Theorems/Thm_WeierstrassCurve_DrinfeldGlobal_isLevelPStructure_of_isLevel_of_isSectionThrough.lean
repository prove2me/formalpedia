-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isLevelPStructure_of_isLevel_of_isSectionThrough
-- name    : WeierstrassCurve.DrinfeldGlobal.isLevelPStructure_of_isLevel_of_isSectionThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c2dba855-ae6c-5878-bcfd-667097ca0350
-- title:
--   Drinfeld Γ(q)-bases yield Katz level-q structures
-- statement:
--   Fix a commutative ring $A$ and a family $\mathcal{G}$ of group laws over $A$, assigning to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant a relative group law on the projective model of $W$; assume $\mathcal{G}$ is chord–tangent (for all such $T$, $W$, $\mathrm{IsUnit}\,W.\Delta$ there is a points-evaluation for $\mathcal{G}\,T\,W$) and has the origin as identity (the identity section is an origin-chart section for a ring homomorphism killing $x/y$ and $z/y$). Let $q$ be a prime with $q \ne 2$, and let $\mathcal{T}$ be a `LevelTransport` datum for $A$, $\mathcal{G}$, $q$ — base-change and variable-change operations on raw Drinfeld pairs, functorial and preserving the level condition — satisfying `IsSectionTransport`, i.e. its transported sections agree with the originals after the corresponding maps of projective models. Let $T$ be an $A$-algebra in which $q$ is a unit, $W$ a projective Weierstrass curve over $T$ which is elliptic, and $u$ a raw Drinfeld pair over $T$ (a curve together with two sections $P$, $Q$) with `RawDrinfeldPair.IsLevel`: $u.\mathrm{curve} = W$, the discriminant of $u.\mathrm{curve}$ is a unit, and $(P,Q)$ is a Drinfeld basis for $\mathcal{G}\,T\,u.\mathrm{curve}$ at $q$ (the basis divisor equals the $q$-torsion ideal). Let $D$ consist of four elements $x_P,y_P,x_Q,y_Q$ of $T$, and suppose $u.P$ factors through the affine chart with coordinates $(x_P,y_P)$ and $u.Q$ with $(x_Q,y_Q)$. Then $D$ is a level-$q$ structure on $W$: both pairs satisfy the affine Weierstrass equation of $W$, $(W.\mathrm{pre}\Psi\,q)$ vanishes at $x_P$ and at $x_Q$, and both products $\prod_{a=1}^{(q-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and its analogue with $x_P$, $x_Q$ interchanged are units in $T$.
--
--   This is the passage from a Drinfeld $\Gamma(q)$-basis to Katz–Mazur style level-$q$ data in terms of affine coordinates, valid when $q$ is invertible on the base; it is the converse direction of the statement that a Katz level-$q$ datum whose coordinates are realised by sections gives a Drinfeld basis, so that at invertible $q$ the two notions agree. It is used in the study of the level moduli problem, in particular in the derivation of primitive roots of unity attached to points of the full-level and $\Gamma_0$-type moduli packages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isLevelPStructure_of_isLevel_of_isSectionThrough.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isLevelPStructure_of_isLevel_of_isSectionThrough
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A T] (hq : IsUnit ((q : ℕ) : T))
    (W : WeierstrassCurve.Projective T) [WeierstrassCurve.IsElliptic W]
    (u : RawDrinfeldPair T) (hu : RawDrinfeldPair.IsLevel 𝒢 q W u)
    (D : ModularCurve.LevelPData T) (hP : IsSectionThrough u.P D.xP D.yP) (hQ : IsSectionThrough u.Q D.xQ D.yQ) :
    ModularCurve.IsLevelPStructure W q D := by sorry
