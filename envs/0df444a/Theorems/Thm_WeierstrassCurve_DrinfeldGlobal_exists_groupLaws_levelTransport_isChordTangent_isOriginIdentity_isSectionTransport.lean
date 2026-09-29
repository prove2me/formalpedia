-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f18a71eb-17a5-5ee1-905b-f9973261bf6e
-- title:
--   Existence of pinned global group laws and level transport
-- statement:
--   Let $A$ be a commutative ring and $q$ a natural number. The assertion is the existence of a pair $(\mathcal G, \mathcal T)$ with five properties. Here $\mathcal G$ is a family of group laws over $A$: for every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ whose discriminant $W.\Delta$ is a unit, a relative group law $\mathcal G\,T\,W\,h_\Delta$ on the Proj model `projModelStrCR W`; and $\mathcal T$ is a `LevelTransport A 𝒢 q`, that is, an operation transporting raw Drinfeld pairs along $A$-algebra maps and an action of Weierstrass variable changes on them, compatible with identities, composition and products, commuting with each other, and preserving the predicate `RawDrinfeldPair.IsLevel 𝒢 q`. The five properties are: (i) $\mathcal G$ is chord–tangent, i.e. for all $T$, $W$, $h_\Delta$ there is an evaluation datum $ev$ with `IsPointsEval W (𝒢 T W hΔ) ev`; (ii) $\mathcal G$ has the origin as identity, i.e. for all $T$, $W$, $h_\Delta$ there is a ring homomorphism $\chi$ from `OriginChartRing W` to $T$ which is an origin-chart section for the unit section $(\mathcal G\,T\,W\,h_\Delta).\mathrm{one}\,(\mathbf 1)$ and kills both `xOverY W` and `zOverY W`; (iii) $\mathcal T$ is a section transport: for each variable change $C$ and raw pair $x$ the curve of $\mathcal T.\mathrm{act}\,C\,x$ equals $C \bullet x.\mathrm{curve}$ and, for every graded homomorphism $\varphi$ of Proj gradings realising $C$ in the sense of `IsVariableChangeHom` and satisfying the irrelevant-ideal condition, the two transported sections $P$, $Q$ composed with the induced `Proj.map φ` recover $x.P$ and $x.Q$; and likewise the curve of $\mathcal T.\mathrm{map}\,f\,x$ is $x.\mathrm{curve}$ base-changed along $f$, with the transported sections recovering $\mathrm{Spec}(f)$ followed by $x.P$, $x.Q$ through any $\varphi$ satisfying `IsCoefficientHom`; (iv) for every $A$-algebra $T$, projective Weierstrass curve $W$ over $T$ and variable change $C$ there exists a graded ring homomorphism $\varphi$ from `projModelGradingCR W` to `projModelGradingCR (C • W)` such that the irrelevant ideal of the target lies in the image of that of the source and `IsVariableChangeHom W C φ` holds, i.e. $\varphi$ fixes constants and sends $X_0 \mapsto u^2X_0 + rX_2$, $X_1 \mapsto u^3X_1 + u^2sX_0 + tX_2$, $X_2 \mapsto X_2$; and (v) for all $A$-algebras $T$, $T'$, every $A$-algebra map $f : T \to T'$ and every $W$ over $T$, a graded ring homomorphism $\varphi$ to `projModelGradingCR (W.map f)` with the same irrelevant-ideal condition and `IsCoefficientHom`, i.e. $\varphi$ acts on constants by $f$ and fixes each coordinate $X_i$. No unit-discriminant hypothesis appears in (iv) and (v).
--
--   This is the packaging statement that produces, over an arbitrary base ring $A$ and for arbitrary level $q$, all the group-law and transport data needed to set up the full-level moduli problem for Weierstrass curves with a pair of $q$-torsion sections: the chord–tangent group law on the Proj model, the normalisation of its identity in the chart at the origin, functorial transport of Drinfeld pairs under base change and variable changes, and the comparison homomorphisms of graded coordinate rings. It is used throughout the full-level representability and $q$-expansion arguments, which take $(\mathcal G, \mathcal T)$ together with these pins as hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
    (A : Type) [CommRing A] (q : ℕ) :
    ∃ (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q),
      𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧ 𝒯.IsSectionTransport ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsVariableChangeHom W C φ) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
        (W : WeierstrassCurve.Projective T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsCoefficientHom W f.toRingHom φ) := by sorry
