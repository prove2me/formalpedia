-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
-- name    : WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/057d0dbe-e08f-5f5d-863c-0ae27dcf61b2
-- title:
--   Rigidity: two relative group laws with the zero section as unit agree on field points
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine Weierstrass curve is elliptic. Assume the base-change hypothesis `hbc`: for every field $K$ carrying an $R$-algebra structure, the fibre product of the structure morphism `projModelStrCR V` (the morphism $\operatorname{Proj}$ of the graded quotient ring of $V$ to $\operatorname{Spec} R$) with $\operatorname{Spec}$ of $R \to K$ is isomorphic, as a scheme, to `projModelCR (V.baseChange K)`. Let $G_0$ and $G_1$ be relative group laws on `projModelStrCR V`, that is, data assigning to each scheme $T$ and each morphism $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $T$-points over $t$ (morphisms $\varphi$ from $T$ to the projective model with $\varphi$ followed by the structure morphism equal to $t$), subject to associativity, both unit laws, left inverses, and compatibility with composition in $T$. Assume further that for every $T$ and every $t : T \to \operatorname{Spec} R$ the underlying morphism of the unit of $G_0$, and likewise of $G_1$, is $t$ followed by the underlying morphism of the zero section `kwZeroSect R V.toAffine`. Then for every field $F$ carrying an $R$-algebra structure and all points $P, Q$ over $\operatorname{Spec}$ of $R \to F$, the two multiplications agree: $G_0.\mathrm{mul}(P,Q) = G_1.\mathrm{mul}(P,Q)$.
--
--   This is the rigidity step in the identification of the group law on a projective Weierstrass model: a relative group law whose unit is the standard zero section at infinity is determined, on field-valued points, by that unit alone. It is used in the comparison of the scheme-theoretic group law with the explicit chord-and-tangent addition, via [`WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comp_projMap_eq_at_field_of_isCoefficientHom`](thm.html#WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comp_projMap_eq_at_field_of_isCoefficientHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G₀ G₁ : RelativeGroupLaw R (projModelStrCR V))
    (hone₀ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1)
    (hone₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G₁.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) :
    ∀ (F : Type u) [Field F] [Algebra R F],
      ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V),
        G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q
          = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q := by sorry
