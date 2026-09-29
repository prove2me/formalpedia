-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
-- name    : WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/abcb8669-905a-59c8-9ec1-a9af92661a37
-- title:
--   Unique lifting of Drinfeld level-q structures along nilpotent thickenings
-- statement:
--   Fix a prime $q$ and a commutative ring $A_0$. Let $\mathcal G$ be a system of group laws over $A_0$, i.e. an assignment, to every $A_0$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ whose discriminant is a unit, of a relative group law on the projective model of $W$; assume $\mathcal G$ is chord–tangent (each such group law admits a points-evaluation, `IsPointsEval`) and has the origin as identity (its identity section is cut out in the origin chart by a ring homomorphism killing $x/y$ and $z/y$). Let $\mathcal T$ be a level transport for $(\mathcal G,q)$: a functorial operation on raw Drinfeld pairs — a projective Weierstrass curve together with two sections of its projective model over the base — along $A_0$-algebra maps and under variable changes, compatible with the level condition; assume $\mathcal T$ is a section transport, i.e. its curve components are the expected base-changed or transformed curves and its two sections pull back to the original ones along the induced maps of projective models. Let $\pi : T \to T'$ be a surjective homomorphism of $A_0$-algebras some power of whose kernel is $0$, and let $E$ be a Weierstrass curve over $T$ with $E.\Delta$ a unit and with $q$ a unit in $T$. Let $x'$ be a raw Drinfeld pair over $T'$ of level $q$ for the base change $E \otimes_T T'$, meaning its curve is that base change, its discriminant is a unit, and its two sections form a Drinfeld basis for $\mathcal G$ at $q$, i.e. their basis divisor equals the $q$-torsion ideal of the group law. Then there is exactly one raw Drinfeld pair $x$ over $T$ of level $q$ for $E$ (in the same sense) with $\mathcal T.\mathrm{map}\,\pi\,x = x'$.
--
--   This is the infinitesimal lifting property of the moduli problem of Drinfeld level-$q$ structures in the sense of Katz–Mazur, in the case where $q$ and the discriminant are invertible, so that the $q$-torsion is finite étale and a Drinfeld basis is an honest basis. It is used in the study of the full-level moduli datum, in particular in the surjectivity and dual-number computations for the associated rigid data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
    (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T T' : Type} [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T']
    (π : T →ₐ[A₀] T') (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (E : WeierstrassCurve T) (hΔ : IsUnit E.Δ) (hq : IsUnit ((q : ℕ) : T))
    (x' : RawDrinfeldPair T') (hx' : RawDrinfeldPair.IsLevel 𝒢 q (E.map π.toRingHom) x') :
    ∃! x : RawDrinfeldPair T, RawDrinfeldPair.IsLevel 𝒢 q E x ∧ 𝒯.map π x = x' := by sorry
