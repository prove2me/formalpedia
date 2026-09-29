-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/307a7790-9323-5c13-9403-cfd130321506
-- title:
--   Points-evaluation transports along a cartesian Proj square
-- statement:
--   Let $T$ and $T'$ be commutative rings, $W$ a projective Weierstrass curve over $T$, and $f : T \to T'$ a ring homomorphism. Let $\varphi$ be a graded ring homomorphism from `projModelGradingCR W` to `projModelGradingCR (W.map f)`, i.e. between the $\mathbb{N}$-graded quotients of the polynomial rings in three variables by the Weierstrass cubic ideals, subject to: the irrelevant ideal of the target is contained in the image under $\varphi$ of the irrelevant ideal of the source (so that `Proj.map φ hφ` exists); `IsCoefficientHom W f φ`, meaning $\varphi$ carries the class of a constant $C\,a$ to the class of $C\,(f a)$ and fixes the classes of the three coordinates $X_i$; and the square formed by `Proj.map φ hφ`, the two structure morphisms `projModelStrCR` to $\operatorname{Spec} T'$ and $\operatorname{Spec} T$, and $\operatorname{Spec}$ of $f$ is cartesian. Let $G$, $G'$ be relative group laws (multiplication, unit, inverse, the group axioms and naturality under base change of the test scheme) on the two $\operatorname{Proj}$ models over $T$, respectively $T'$. Assume $\varphi$ is multiplicative in the sense that for every scheme $S$, every $s : S \to \operatorname{Spec} T'$ and all sections $x,y$ of the $T'$-model over $s$, the morphism underlying $G'.mul\ s\ x\ y$ followed by `Proj.map φ hφ` equals the morphism underlying the $G$-product of the composites of $x$ and $y$ with `Proj.map φ hφ`, taken over $s$ followed by $\operatorname{Spec}$ of $f$. Finally assume given a family $ev$ of bijections, for each field $F$ with a $T$-algebra structure, from sections of the $T$-model over $\operatorname{Spec}$ of $T \to F$ to the affine points of $W$ base changed to $F$, satisfying `IsPointsEval W G ev`: it is additive for $G.mul$ and equivariant for Galois twists, $ev_F(\mathrm{galTwist}\,\sigma\,P) = \mathrm{Point.map}\ \sigma\ (ev_F P)$ for $\sigma : F \simeq_{T} F$. The conclusion is that there exists a corresponding family $ev'$ of bijections for $W.map\ f$ over fields $F$ with a $T'$-algebra structure satisfying `IsPointsEval (W.map f) G' ev'`.
--
--   This is the transport step for the identification of field-valued points of the projective Weierstrass model with affine chord–tangent points: from a base where such an identification is known it is carried along a cartesian square coming from a coefficient homomorphism. It is used in the construction of a relative group law with prescribed unit section on models over rings where the discriminant is a unit, and in the comparison of origin charts with scheme-theoretic multiplication by $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
      (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw T (projModelStrCR W)) (G' : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver s (projModelStrCR (W.map f))),
      (G'.mul s x y).1 ≫ Proj.map φ hφ =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) ≃
        (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev) :
    ∃ ev' : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T' F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f)) ≃
          ((W.map f).baseChange F).toAffine.Point,
      IsPointsEval (W.map f) G' ev' := by sorry
