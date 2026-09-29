-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
-- name    : WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/41eb9303-cdb2-550e-b27c-710afd006ead
-- title:
--   Transport of a relative group law along a cartesian Proj square
-- statement:
--   Let $T$ and $T'$ be commutative rings (in a fixed universe), let $V$ be a Weierstrass curve in projective form over $T$ whose associated affine curve is elliptic, and let $f : T \to T'$ be a ring homomorphism. Let $\varphi$ be a graded ring homomorphism from the quotient grading `projModelGradingCR V` of the projective Weierstrass model of $V$ to that of the base-changed curve $V.\mathrm{map}\ f$, subject to the hypothesis $h\varphi$ that the irrelevant ideal of the target is contained in the image under $\varphi$ of the irrelevant ideal of the source (so that $\mathrm{Proj}.\mathrm{map}\ \varphi\ h\varphi$ is defined), and assume `IsCoefficientHom V f φ`, i.e. $\varphi$ carries the class of a constant $C\,a$ to the class of $C\,(f a)$ for every $a \in T$ and fixes the classes of the three coordinates $X_i$. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj} \to \operatorname{Spec} T$ of the model of $V$, and $L$ one on the structure morphism $\mathrm{Proj} \to \operatorname{Spec} T'$ of the model of $V.\mathrm{map}\ f$; such a law consists of a fibrewise multiplication, unit and inverse on sections $\{\psi : Y \to \mathrm{Proj} \mid \psi \text{ over the base morphism}\}$, satisfying associativity, the unit laws, left inversion, and naturality of multiplication in the base. Assume further that the unit section of $L$ over the identity of $\operatorname{Spec} T'$, followed by $\mathrm{Proj}.\mathrm{map}\ \varphi\ h\varphi$, equals $\operatorname{Spec}(f)$ followed by the unit section of $G$ over the identity of $\operatorname{Spec} T$, and that the square formed by $\mathrm{Proj}.\mathrm{map}\ \varphi\ h\varphi$, the two structure morphisms and $\operatorname{Spec}(f)$ commutes. Then for every scheme $S$, every $s : S \to \operatorname{Spec} T'$ and all sections $x, y$ of the model of $V.\mathrm{map}\ f$ over $s$, the product $L.\mathrm{mul}\ s\ x\ y$ followed by $\mathrm{Proj}.\mathrm{map}\ \varphi\ h\varphi$ coincides with the $G$-product, over $s$ followed by $\operatorname{Spec}(f)$, of $x$ and $y$ each followed by $\mathrm{Proj}.\mathrm{map}\ \varphi\ h\varphi$.
--
--   This is the compatibility statement saying that the group law on the projective Weierstrass model of a base-changed elliptic curve is the base change of the group law downstairs, once the two unit sections are known to correspond; it is the form in which the group law is transported across the cartesian square attached to a coefficient-preserving graded homomorphism. It is used in the construction and comparison of Drinfeld level structures on Weierstrass models, for instance in the statements about sections which are Drinfeld bases over a base change and in the verification of commutativity of the transported law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
    {T T' : Type u} [CommRing T] [CommRing T'] (V : WeierstrassCurve.Projective T) [V.toAffine.IsElliptic]
    (f : T →+* T')
    (φ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ)
    (hcoef : IsCoefficientHom V f φ)
    (G : RelativeGroupLaw T (projModelStrCR V)) (L : RelativeGroupLaw T' (projModelStrCR (V.map f)))
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1)
    (hsq : Proj.map φ hφ ≫ projModelStrCR V = projModelStrCR (V.map f) ≫ Spec.map (CommRingCat.ofHom f))
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver s (projModelStrCR (V.map f))) :
    (L.mul s x y).1 ≫ Proj.map φ hφ =
      (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
        ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1 := by sorry
