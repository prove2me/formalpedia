-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_isCommutative_one_eq_zeroSect_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/51bee43f-f5b0-5cbc-8e67-81f220e17616
-- title:
--   Translating a commutative relative group law to the zero section
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$, with associated structure morphism $\pi =$ `projModelStrCR V` from the $\mathrm{Proj}$ of the graded quotient of $R[X_0,X_1,X_2]$ by the homogeneous Weierstrass ideal of $V$ to $\operatorname{Spec} R$ (the map induced by $\mathrm{Proj}\to\operatorname{Spec}$ of the degree-zero part together with the structure map from $R$). Let $G_1$ be a `RelativeGroupLaw` for $\pi$, that is: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi : T \to \mathrm{Proj} \mid \varphi$ followed by $\pi$ equals $t\}$ of $T$-points over $t$, subject to associativity, the two unit laws, left inverses, and compatibility of the multiplication with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume that the multiplication of $G_1$ is commutative for every such $t$. Then there exists a relative group law $G_0$ for $\pi$ whose multiplication is again commutative for every $t$, and whose unit at $t$ has underlying morphism $t$ followed by the underlying morphism of the section `kwZeroSect R V.toAffine`, the zero section $[0:1:0]$ of the projective model.
--
--   The standard translation trick: any commutative group law on a curve can be moved so that its neutral element becomes a prescribed point, here the zero section of the projective Weierstrass model. It is used in the construction of relative group laws on Weierstrass models arising in the Čerednik–Drinfel'd part of the development, where the group law produced by other means need not have the zero section as unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.exists_isCommutative_one_eq_zeroSect_of_isCommutative
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (G₁ : RelativeGroupLaw R (projModelStrCR V))
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (x y : SchemeHomOver t (projModelStrCR V)), G₁.mul t x y = G₁.mul t y x) :
    ∃ G₀ : RelativeGroupLaw R (projModelStrCR V),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR V)), G₀.mul t x y = G₀.mul t y x)
      ∧ (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) := by sorry
