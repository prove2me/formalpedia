-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
-- name    : WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e3028ee4-8fdd-5ee5-ae71-0869335fa475
-- title:
--   Sections of a transported Drinfeld pair pass through f-images
-- statement:
--   Let $A$ be a commutative ring, $\mathcal{G}$ a family of relative group laws on the projective Weierstrass models over $A$-algebras with unit discriminant, $q$ a natural number, and $\mathcal{T}$ a `LevelTransport` for $A$, $\mathcal{G}$, $q$, assumed to satisfy `IsSectionTransport`: for each variable change and each $A$-algebra map the transported curve agrees with the expected one, and, after the resulting identification, the two sections of the transported pair composed with $\mathrm{Proj}$ of any graded homomorphism of the relevant type recover the original sections, respectively their base changes along $\mathrm{Spec}$ of the map. Let $T$, $T'$ be commutative $A$-algebras, $f : T \to T'$ an $A$-algebra homomorphism, and $x$ a raw Drinfeld pair over $T$, i.e. a projective Weierstrass curve $x.\mathrm{curve}$ together with two sections $x.P$, $x.Q$. Assume there exists a graded ring homomorphism $\varphi$ from the graded quotient ring of $x.\mathrm{curve}$ to that of $x.\mathrm{curve}$ base changed along $f$, whose image of the irrelevant ideal dominates the irrelevant ideal of the target, and which is a coefficient homomorphism for $f$: it carries the class of a constant $C\,a$ to the class of $C\,(f a)$ and fixes the classes of the three coordinates $X_i$. Let $D$ be level $P$-data over $T$, consisting of elements $x_P, y_P, x_Q, y_Q$ of $T$, and suppose $x.P$ passes through $(x_P, y_P)$ and $x.Q$ through $(x_Q, y_Q)$, in the sense that there is a ring homomorphism $\chi$ from the $Z$-chart ring of $x.\mathrm{curve}$ to $T$ satisfying `IsZChartSection` for the section and having the prescribed affine coordinates $\mathrm{affX}\,\chi$, $\mathrm{affY}\,\chi$. Then the two sections of the transported pair $\mathcal{T}.\mathrm{map}\,f\,x$ pass through $(f(x_P), f(y_P))$ and $(f(x_Q), f(y_Q))$ respectively.
--
--   This is the naturality statement for the chart description of the two marked sections of a Drinfeld pair: passing through a point with given affine coordinates is preserved by base change along an $A$-algebra map, the coordinates being transformed by the map itself. It is used in the comparison of level structures with their coordinate data, for instance in the identifications of transported pairs with relabelled rigid data and in the computation of the Weil pairing under such transports.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport.lean

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

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : RawDrinfeldPair T)

    (hCO : ∃ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsCoefficientHom x.curve f.toRingHom φ)
    (D : ModularCurve.LevelPData T)
    (hP : IsSectionThrough x.P D.xP D.yP) (hQ : IsSectionThrough x.Q D.xQ D.yQ) :
    IsSectionThrough (𝒯.map f x).P (f D.xP) (f D.yP) ∧ IsSectionThrough (𝒯.map f x).Q (f D.xQ) (f D.yQ) := by sorry
