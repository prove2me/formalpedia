-- Prove2me | Theorems.Thm_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
-- name    : WeierstrassProjModel.isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/456a9983-9e06-5abd-a677-bea409dd8e0a
-- title:
--   n-torsion of a projective Weierstrass model is finite and flat
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine curve is elliptic (its discriminant is a unit). Write $f =$ `projModelStrCR V` for the structure morphism $\operatorname{Proj}$ of the graded quotient of the polynomial ring in three variables by the homogeneous Weierstrass ideal, followed by the morphism of spectra induced by $R \to$ (degree-zero part), to $\operatorname{Spec} R$. Let $G$ be a relative group law on $f$: for every $R$-scheme $t : T \to \operatorname{Spec} R$ a multiplication, unit and inverse on the set of $\varphi : T \to \operatorname{Proj}$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the unit laws, left inverses, and naturality of multiplication under base change along $\psi : T' \to T$ over $\operatorname{Spec} R$. Let $ev$ be a family, indexed by fields $F$ that are $R$-algebras, of bijections between the $\operatorname{Spec} F$-points of $f$ over $R$ and the affine points of $V$ base changed to $F$, and assume `IsPointsEval V G ev`: each $ev_F$ carries the group law $G$ to addition of points, and intertwines twisting by $\sigma \in \operatorname{Aut}_R(F)$ with `Point.map` of $\sigma$. Let $n > 0$. Then the morphism `G.schemeKerStr n` to $\operatorname{Spec} R$ — the second projection of the fibre product of the multiplication-by-$n$ endomorphism `G.schemeNsmul n` of $\operatorname{Proj}$ with the unit section of $f$ — is finite, flat and locally of finite presentation.
--
--   This is the statement that the $n$-torsion subscheme $E[n]$ of the projective Weierstrass model of an elliptic curve over an arbitrary base ring is a finite flat group scheme of finite presentation over the base, in the form needed for representability questions for level structures. It is used in the construction and study of Drinfeld level structures on such models, in particular for comparing torsion ideals with divisor bases and for the representability of raw Drinfeld pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic.lean

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

theorem WeierstrassProjModel.isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) {n : ℕ} (hn : 0 < n) :
    IsFinite (G.schemeKerStr n) ∧ Flat (G.schemeKerStr n) ∧ LocallyOfFinitePresentation (G.schemeKerStr n) := by sorry
