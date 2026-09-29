-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/793d8a0b-a322-5c00-97c1-f1dff3fc943f
-- title:
--   Lifting Drinfeld q-level structures along Ω[ε]→Ω
-- statement:
--   Fix a prime $q\neq 2$ and a commutative ring $A$. Let $\mathcal G$ be a family of group laws, assigning to each $A$-algebra $T$ and each Weierstrass curve $W$ over $T$ with invertible discriminant a relative group law on the projective model of $W$, subject to two conditions: `IsChordTangent`, that each such group law admits a points-evaluation, and `IsOriginIdentity`, that its unit section is cut out by a ring homomorphism from the origin chart killing $x/y$ and $z/y$. Let $\mathcal T$ be a `LevelTransport` for $\mathcal G$ and $q$, i.e. functorial base-change and variable-change operations on raw Drinfeld pairs (a curve together with two sections) preserving the level condition, satisfying `IsSectionTransport`: the transported sections pull back to the original ones along the induced maps of Proj. Assume further that for every $A$-algebra map $f\colon T\to T'$ and every Weierstrass curve $W$ over $T$ there is a graded ring homomorphism between the graded projective-model rings of $W$ and of $W$ base-changed along $f$ which is a coefficient homomorphism (sending $C\,a$ to $C\,(f a)$ and each $X_i$ to $X_i$) and for which the irrelevant ideal of the target is contained in the image of that of the source. Let $\Omega$ be an algebraically closed field of characteristic $0$ which is an $A$-algebra, with $q\neq 0$ in $\Omega$, let $W$ be a Weierstrass curve over the dual numbers $\Omega[\varepsilon]$ with $\Delta_W$ a unit, and let $z_0$ be a raw Drinfeld pair over $\Omega$ which is of level $q$ for the reduction of $W$ along $\mathrm{fst}\colon\Omega[\varepsilon]\to\Omega$, meaning that its curve equals that reduction and its two sections form a Drinfeld basis of $q$-torsion for the corresponding group law. Then there is a raw Drinfeld pair $z$ over $\Omega[\varepsilon]$ which is of level $q$ for $W$ and whose transport along $\mathrm{fst}$ equals $z_0$ exactly.
--
--   This is the infinitesimal lifting (formal smoothness) property of the moduli problem of Drinfeld $\Gamma(q)$-structures at an invertible level $q$: level structures on an elliptic curve over $\Omega[\varepsilon]$ are determined by, and lift from, their reductions modulo $\varepsilon$. It is used in the construction of points of the full-level modular curve over the dual numbers that reduce to a prescribed point, with prescribed behaviour under the $\Gamma_0$-type operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem WeierstrassCurve.DrinfeldGlobal.exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : Type) [CommRing A]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (W : WeierstrassCurve (DualNumber Ω)) (hW : IsUnit W.Δ)
    (z₀ : RawDrinfeldPair Ω)
    (hz₀ : RawDrinfeldPair.IsLevel 𝒢 q (W.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).toRingHom) z₀) :
    ∃ z : RawDrinfeldPair (DualNumber Ω),
      RawDrinfeldPair.IsLevel 𝒢 q W z ∧ 𝒯.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A) z = z₀ := by sorry
