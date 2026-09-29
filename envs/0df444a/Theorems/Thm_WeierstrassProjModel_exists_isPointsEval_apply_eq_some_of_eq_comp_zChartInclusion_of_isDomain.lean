-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
-- name    : WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/f22c68e2-4b69-5973-affa-d39c05ac665d
-- title:
--   Coordinate-reading points-evaluation for the projective Weierstrass model
-- statement:
--   Let $T$ be a Noetherian commutative domain and let $W$ be a Weierstrass curve over $T$ that is elliptic (its discriminant is a unit). Let $G$ be a relative group law on the structure morphism $\mathrm{projModelStrCR}\,W.\mathrm{toProjective} : \mathrm{Proj} \to \operatorname{Spec} T$ of the projective Weierstrass model, i.e. a functorially compatible group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of sections over each $t : T' \to \operatorname{Spec} T$, and assume that the underlying morphism of its unit over the identity of $\operatorname{Spec} T$ is that of the zero section `kwZeroSect`. Then there exists a family $\mathrm{ev}$ assigning to each field $F$ with a $T$-algebra structure a bijection between the $F$-points of the projective model over $\operatorname{Spec}(T \to F)$ and the group of affine points of the base change $W_F$, such that: (i) `IsPointsEval` holds, that is each $\mathrm{ev}_F$ carries $G$-multiplication to addition of affine points and is equivariant for the twisting action of $\mathrm{Aut}_T(F)$, $\mathrm{ev}_F(\sigma \cdot P) = \sigma_*(\mathrm{ev}_F(P))$; (ii) $\mathrm{ev}_F$ sends the point obtained by composing $\operatorname{Spec}(T \to F)$ with the zero section to $0$; and (iii) whenever a point $P$ factors as $\operatorname{Spec}$ of a ring homomorphism $\chi : \mathrm{ZChartRing}\,W.\mathrm{toProjective} \to F$ followed by the chart inclusion `zChartι`, the pair $(\chi(X/Z), \chi(Y/Z))$ is a nonsingular point of the affine curve $W_F$ and $\mathrm{ev}_F(P)$ is the affine point with these coordinates.
--
--   This identifies the abstract relative group law on the projective Weierstrass model with the classical chord–tangent group law on affine points, in the normalised form that reads coordinates: on the chart $Z \neq 0$ the evaluation returns the values of $X/Z$ and $Y/Z$, which pins down $\mathrm{ev}$ beyond what `IsPointsEval` alone determines (the latter allows composition with negation). It is used in the study of level structures on Drinfeld-type pairs, where sections of the model must be compared with explicit coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain.lean

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

theorem WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
    {T : Type} [CommRing T] [IsDomain T] [IsNoetherianRing T] (W : WeierstrassCurve T) [W.IsElliptic]
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
