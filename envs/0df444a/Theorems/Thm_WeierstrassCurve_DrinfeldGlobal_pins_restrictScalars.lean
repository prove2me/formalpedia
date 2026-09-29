-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_pins_restrictScalars
-- name    : WeierstrassCurve.DrinfeldGlobal.pins_restrictScalars
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/62230493-b3c3-51e8-a1dd-f463e63c07bd
-- title:
--   Transfer of the Drinfeld level pins under restriction of scalars
-- statement:
--   Let $A_0$ be a commutative ring, $A$ a commutative $A_0$-algebra (both in a fixed universe), and $q$ a natural number. Let $\mathcal G_0 :$ `GroupLaws` $A_0$ be a family assigning to each $A_0$-algebra $T$, each projective Weierstrass curve $W$ over $T$ and each proof that $\Delta_W$ is a unit a relative group law on the projective model of $W$, and assume: (i) $\mathcal G_0$ is chord–tangent, i.e. for all such $T, W, h_\Delta$ there is an evaluation `ev` with `IsPointsEval` $W\,(\mathcal G_0\,T\,W\,h_\Delta)\,$`ev`; (ii) $\mathcal G_0$ has the origin as identity, i.e. for all such $T, W, h_\Delta$ there is a ring homomorphism $\chi$ from the origin-chart ring of $W$ to $T$ which is an origin-chart section of the unit of $\mathcal G_0\,T\,W\,h_\Delta$ and kills $x/y$ and $z/y$. Let $\mathcal T_0$ be a `LevelTransport` for $A_0$, $\mathcal G_0$, $q$ (functorial transport of raw Drinfeld pairs along $A_0$-algebra maps and along Weierstrass variable changes, preserving the level-$q$ condition), assumed to be a section transport: for every variable change $C$ and pair $x$, the curve of $\mathcal T_0.\mathrm{act}\,C\,x$ is $C\cdot x.\mathrm{curve}$ and for every graded homomorphism $\varphi$ between the projective-model gradings realising $C$ (with the irrelevant-ideal condition) the transported sections $P, Q$ pull back along `Proj.map` $\varphi$ to the original ones; and likewise for $\mathcal T_0.\mathrm{map}\,f$ with $\varphi$ a coefficient homomorphism, the transported sections composing to $\mathrm{Spec}(f)$ followed by the original sections. Finally assume (iii) that for all $A_0$-algebras $T, T'$, every $A_0$-algebra map $f : T \to T'$ and every projective Weierstrass curve $W$ over $T$ there exists a graded ring homomorphism $\varphi$ from `projModelGradingCR` $W$ to `projModelGradingCR` $(W.\mathrm{map}\,f)$, with the irrelevant ideal of the target contained in the image under $\varphi$ of that of the source, satisfying `IsCoefficientHom`, i.e. $\varphi$ sends the class of a constant $C(a)$ to the class of $C(f(a))$ and fixes the classes of the three coordinates. Then the four corresponding assertions hold over $A$: $\mathcal G_0.\mathrm{restrictScalars}\,A$ is chord–tangent and has the origin as identity, $\mathcal T_0.\mathrm{restrictScalars}\,A$ is a section transport, and coefficient-homomorphism realisations exist for all $A$-algebras $T, T'$ and all $A$-algebra maps between them.
--
--   This is the compatibility statement accompanying the restriction-of-scalars construction on guarded group-law families and level transports: all the hypotheses ("pins") used to run the Drinfeld level-$q$ moduli construction over a base $A_0$ persist over any $A_0$-algebra $A$. It is invoked throughout the analysis of the level moduli package attached to rigid Weierstrass data, for instance in the flatness and reducedness statements for the full-level diamond constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_pins_restrictScalars.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem WeierstrassCurve.DrinfeldGlobal.pins_restrictScalars
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q : ℕ)
    (𝒢₀ : GroupLaws A₀) (h𝒢₀ : 𝒢₀.IsChordTangent) (h𝒢O₀ : 𝒢₀.IsOriginIdentity)
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q) (h𝒯₀ : 𝒯₀.IsSectionTransport)
    (hCO₀ : ∀ (T T' : Type u) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    (𝒢₀.restrictScalars A).IsChordTangent ∧ (𝒢₀.restrictScalars A).IsOriginIdentity ∧
    (𝒯₀.restrictScalars A).IsSectionTransport ∧
    (∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) := by sorry
