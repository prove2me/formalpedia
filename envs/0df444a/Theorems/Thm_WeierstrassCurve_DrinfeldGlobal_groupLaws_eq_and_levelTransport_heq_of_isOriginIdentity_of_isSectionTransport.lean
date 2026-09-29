-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport
-- name    : WeierstrassCurve.DrinfeldGlobal.groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/0032d63b-ab3a-5a29-827a-8aad6ed53a97
-- title:
--   Uniqueness of origin-pinned group laws and their level transports
-- statement:
--   Let $A$ be a commutative ring and $q$ a natural number. Let $\mathcal G,\mathcal G'$ be two families of group laws over $A$, each assigning to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with unit discriminant a relative group law on the structure morphism $\mathtt{projModelStrCR}\,W$ of the projective model, and assume both are origin-pinned in the sense of `GroupLaws.IsOriginIdentity`: for every such $T$, $W$ and every witness that $\Delta_W$ is a unit there is a ring homomorphism $\chi$ from the origin-chart ring of $W$ to $T$ which realises the unit section of the group law over the identity base as an origin-chart section and kills both $x/y$ and $z/y$. Let $\mathcal T$ and $\mathcal T'$ be level transports of levels $q$ over $\mathcal G$ and $\mathcal G'$ respectively, that is, operations transporting raw Drinfeld pairs (a curve together with two sections) along $A$-algebra maps and along variable changes, functorial and equivariant in the sense of the structure fields, and preserving the level condition; assume both satisfy `IsSectionTransport`, i.e. the transported curve is the expected one ($C \bullet W$, resp. $W$ with coefficients pushed along $f$) and, for every graded homomorphism $\varphi$ of projective-model gradings satisfying the irrelevant-ideal inclusion and realising the variable change (constants fixed, $X_0 \mapsto u^2X_0 + rX_2$, $X_1 \mapsto u^3X_1 + u^2sX_0 + tX_2$, $X_2\mapsto X_2$), respectively the coefficient map (constants $a \mapsto f(a)$, $X_i \mapsto X_i$), the two transported sections composed with $\mathrm{Proj}\,\varphi$ recover the original sections, respectively their base changes along $\operatorname{Spec} f$. Assume further that such realising graded homomorphisms exist for every variable change over every $A$-algebra (hypothesis $hVC$) and for every $A$-algebra homomorphism (hypothesis $hCO$). Then $\mathcal G = \mathcal G'$, and $\mathcal T$ and $\mathcal T'$ are heterogeneously equal.
--
--   This is the uniqueness counterpart to the existence of a global group law on projective Weierstrass models with invertible discriminant together with its transport data on Drinfeld level structures: the origin pinning and the section-transport pinning determine both objects completely. It is used in the construction and analysis of full-level moduli packages, for instance in the flatness, reducedness and completion statements for the moduli data attached to powers of the rigid Weierstrass datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport.lean

import Mathlib
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

universe u

open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.groupLaws_eq_and_levelTransport_heq_of_isOriginIdentity_of_isSectionTransport
    (A : Type u) [CommRing A] (q : ℕ)
    (𝒢 𝒢' : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity) (h𝒢O' : 𝒢'.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (𝒯' : LevelTransport A 𝒢' q) (h𝒯 : 𝒯.IsSectionTransport) (h𝒯' : 𝒯'.IsSectionTransport)

    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    𝒢 = 𝒢' ∧ HEq 𝒯 𝒯' := by sorry
