-- Prove2me | Theorems.Thm_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic
-- name    : WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/e3b040f6-dbbe-55fb-b582-7bcaa3f6e34b
-- title:
--   Rigidity lemma for projective Weierstrass models over a ring
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine curve satisfies `IsElliptic`. Write $E = \operatorname{projModelCR} V$ for the $\mathrm{Proj}$ of the graded quotient ring attached to $V$ (the quotient of the polynomial ring in three homogeneous variables by the homogeneous ideal of $V$, with its induced grading) and $\pi = \operatorname{projModelStrCR} V : E \to \operatorname{Spec} R$ for its structure morphism, namely $\mathrm{Proj}.\mathrm{toSpecZero}$ followed by the map of spectra induced by $R \to (\text{degree-}0\text{ part})$. Assume given a section $e : \operatorname{Spec} R \to E$ of $\pi$, so $e$ followed by $\pi$ is the identity, and a morphism $\varphi : E \times_{\operatorname{Spec} R} E \to E$ from the fibre product of $\pi$ with itself such that $\varphi$ followed by $\pi$ equals the first projection followed by $\pi$; thus $\varphi$ is a morphism over $R$. Assume further that $\varphi$ is constant along the slice given by $e$: the morphism $E \to E \times_{\operatorname{Spec} R} E$ with components $\mathrm{id}_E$ and $\pi$ followed by $e$, composed with $\varphi$, equals $\pi$ followed by $e$. The conclusion is that $\varphi$ equals the second projection followed by the composite of the morphism $E \to E \times_{\operatorname{Spec} R} E$ with components ($\pi$ followed by $e$, $\mathrm{id}_E$) with $\varphi$; the compatibility conditions for both liftings are supplied by the section identity for $e$.
--
--   This is Mumford's rigidity lemma in the form needed for the projective Weierstrass model of an elliptic curve over an arbitrary commutative base ring: a morphism $E \times_R E \to E$ over $R$ that is constant along the slice through the section $e$ factors through the second projection. It is used to prove rigidity of relative group laws, in [`WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic), via the field case of the statement together with properness and integrality of the model and the base-change description of its fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (e : Spec (CommRingCat.of R) ⟶ projModelCR V) (he : e ≫ projModelStrCR V = 𝟙 _)
    (φ : pullback (projModelStrCR V) (projModelStrCR V) ⟶ projModelCR V)
    (hφ : φ ≫ projModelStrCR V = pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
    (hconst : pullback.lift (𝟙 (projModelCR V)) (projModelStrCR V ≫ e)
        (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ φ = projModelStrCR V ≫ e) :
    φ = pullback.snd (projModelStrCR V) (projModelStrCR V) ≫
      (pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V))
        (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ φ) := by sorry
