-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep
-- name    : WeierstrassProjModel.kw_ev_triple_projections_chartFactor_pointClass_indep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/1934d132-7c6c-5350-b46f-feaad1984b33
-- title:
--   Independent chart factorisations of the three projections of E³
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ which is elliptic, so that its discriminant $\Delta$ is a unit. Write $\pi\colon E=\operatorname{Proj}$ of the graded quotient $R[X_0,X_1,X_2]/(W_{\mathrm{proj}})$ $\to\operatorname{Spec}R$ for `projModelStrCR W.toProjective`; it is smooth of relative dimension $1$ and geometrically integral, whence the iterated pullback $X_3=(E\times_R E)\times_R E$ is integral. Give $K=X_3$`.functionField` the $R$-algebra structure obtained from the composite of $\operatorname{Spec}$ of the stalk at the generic point of $X_3$ with the second outer projection followed by $\pi$; then $\Delta$ has nonzero image in $K$. The assertion is the existence of indices $i_a,i_b,i_c\in\{0,1,2\}$ and $R$-algebra maps $\psi_a,\psi_b,\psi_c$ from the homogeneous localisations of the model away from the classes of $X_{i_a},X_{i_b},X_{i_c}$ into $K$ such that each of the three coordinate projections $\operatorname{Spec}K\to E$ (first and second components of the inner pullback composed with the outer first projection, and the outer second projection) equals $\operatorname{Spec}$ of the corresponding $\psi$ followed by the associated affine chart inclusion of `projModelAffineOpenCoverCR`, and that the point classes $c_\bullet=\llbracket(\psi_\bullet(\mathrm{gen}\,i_\bullet\,k))_{k}\rrbracket$ in $\mathbb{P}^2(K)$ satisfy $c_a\neq c_b$, $c_b\neq c_c$, $c_a\oplus c_b\neq c_c$ and $c_a\neq c_b\oplus c_c$, where $\oplus$ is the `addMap` of the projective Weierstrass curve $(W_K)_{\mathrm{proj}}$.
--
--   This is the point-class level form of the genericity statement that the three coordinates of the generic point of the triple self-product $E^3$ are in general position with respect to the group law: no two coincide and neither is the sum of the other two in the relevant order. It is used by [`WeierstrassProjModel.kw_ev_triple_projections_indep`](thm.html#WeierstrassProjModel.kw_ev_triple_projections_indep), which transports these inequalities to the level of points of the curve over the function field, as needed when verifying identities (such as associativity) by a density argument on $E^3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem WeierstrassProjModel.kw_ev_triple_projections_chartFactor_pointClass_indep
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    let X3 : Scheme.{u} :=
      pullback (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
    haveI : IsIntegral X3 := by
      haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
        LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : IsIntegral (projModelCR W.toProjective) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : GeometricallyIntegral (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      haveI : IsIntegral ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : IsLocallyNoetherian ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : GeometricallyIntegral (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    letI : Algebra R X3.functionField :=
      (Spec.preimage (X3.fromSpecStalk (genericPoint X3)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R X3.functionField W.Δ ≠ 0 := (W.isUnit_Δ.map _).ne_zero
    ∃ (ia : Fin 3) (ψa : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ia : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField)
      (ib : Fin 3) (ψb : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ib : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField)
      (ic : Fin 3) (ψc : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ic : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField),
      (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψa.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ia)
      ∧ (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψb.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ib)
      ∧ (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψc.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ic)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧)
      ∧ ((kw_lrApt_WF W X3.functionField).addMap
            ⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ (kw_lrApt_WF W X3.functionField).addMap
              ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
              ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧) := by sorry
