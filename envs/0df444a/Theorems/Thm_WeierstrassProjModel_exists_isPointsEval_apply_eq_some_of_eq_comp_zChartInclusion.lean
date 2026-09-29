-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
-- name    : WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/aaf1b3f2-7443-5bbe-a9b5-f5ec3e2f4461
-- title:
--   Coordinate-reading points evaluation for the projective Weierstrass model
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$ whose discriminant $\Delta_W$ is a unit. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj}$ of the graded Weierstrass model $W^{\mathrm{proj}}$ over $\operatorname{Spec} T$, that is, functorially given multiplication, unit and inverse on the sets of sections $\{\varphi : S \to \mathrm{Proj} \mid \varphi \text{ over } s\}$ for all $T$-schemes $s : S \to \operatorname{Spec} T$, satisfying the group axioms and naturality of multiplication under base change; assume that the unit of $G$ at the identity of $\operatorname{Spec} T$ is the zero section `kwZeroSect`, the $T$-point landing in the chart where the $Y$-coordinate is invertible. Then there is a family of bijections $\mathrm{ev}_F$, indexed by fields $F$ with a $T$-algebra structure, from the $T$-morphisms $\operatorname{Spec} F \to \mathrm{Proj}$ to the affine points of the base change $W_F$, such that: $\mathrm{ev}$ is a points evaluation, i.e. it carries $G$-multiplication to addition of affine points and satisfies $\mathrm{ev}_F(\sigma^\ast P) = \sigma_\ast(\mathrm{ev}_F(P))$ for every $\sigma \in \mathrm{Aut}_T(F)$; the base change of the zero section to $F$ has $\mathrm{ev}_F$-value $0$; and whenever a point $P$ factors as $\operatorname{Spec}$ of a ring homomorphism $\chi : \mathrm{ZChartRing}(W^{\mathrm{proj}}) \to F$ followed by the inclusion $\iota_{D_+(Z)}$ of the $Z$-chart, the pair $(\chi(X/Z), \chi(Y/Z))$ is nonsingular on $W_F$ and $\mathrm{ev}_F(P)$ is the corresponding affine point.
--
--   This fixes, among the group-law-compatible identifications of $\operatorname{Spec} F$-points of the projective Weierstrass model with affine points of $W_F$ (which are determined only up to Galois-equivariant additive automorphisms), the one that reads off the affine coordinates $X/Z$, $Y/Z$ on the chart $D_+(Z)$, for a Weierstrass curve with invertible discriminant over an arbitrary base ring. It is used in the construction of quaternionic group laws and point identifications in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion
    {T : Type} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw T (projModelStrCR W.toProjective))
    (hG : (G.one (𝟙 _)).1 = (kwZeroSect T W).1) :
    ∃ ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W.toProjective) ≃
          (W.toProjective.baseChange F).toAffine.Point,
      IsPointsEval W.toProjective G ev ∧
      (∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F],
        ev F ⟨Spec.map (CommRingCat.ofHom (algebraMap T F)) ≫ (kwZeroSect T W).1,
          by rw [Category.assoc, (kwZeroSect T W).2, Category.comp_id]⟩ = 0) ∧
      ∀ (F : Type) [Field F] [DecidableEq F] [Algebra T F]
        (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W.toProjective))
        (χ : ZChartRing W.toProjective →+* F),
        P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective →
        ∃ hxy : (W.toProjective.baseChange F).toAffine.Nonsingular (χ (xOverZ W.toProjective)) (χ (yOverZ W.toProjective)),
          ev F P = WeierstrassCurve.Affine.Point.some _ _ hxy := by sorry
