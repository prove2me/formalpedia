-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_chartFactor_addMap_self_ne_zeroClass
-- name    : WeierstrassProjModel.kw_ev_genericPoint_chartFactor_addMap_self_ne_zeroClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/41054925-30c5-5eb8-a807-8fd93ae7a623
-- title:
--   Generic point of an elliptic model: chart factorisation with 2P≠[0:1:0]
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ which is elliptic (so that its discriminant $\Delta$ is a unit). Write $E=\operatorname{Proj}$ of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(W_{\mathrm{proj}})$, graded by the images of the homogeneous submodules, with structure morphism $E\to\operatorname{Spec}R$ obtained from $\operatorname{Proj}\to\operatorname{Spec}$ of degree zero followed by $\operatorname{Spec}$ of $R\to(\text{degree }0)$. This morphism is smooth (being smooth of relative dimension $1$) and geometrically integral (via the isomorphisms between its base changes and the projective models of the base-changed curve), hence $E$ is an integral scheme; its function field $F=K(E)$ carries the $R$-algebra structure coming from the composite $\operatorname{Spec}\mathcal O_{E,\eta}\to E\to\operatorname{Spec}R$ at the generic point $\eta$, and the image of $\Delta$ in $F$ is nonzero. The assertion is that there are an index $i\in\{0,1,2\}$ and an $R$-algebra homomorphism $\psi$ from the homogeneous localisation away from the class of $X_i$ to $F$ such that the canonical morphism $\operatorname{Spec}\mathcal O_{E,\eta}\to E$ equals $\operatorname{Spec}(\psi)$ followed by the $i$-th inclusion of the standard affine open cover of $E$, and such that the addition map of the projective Weierstrass curve $(W\otimes_R F)_{\mathrm{proj}}$, applied to the class of the triple $(\psi(\mathrm{gen}\,i\,k))_{k}$ with itself, is not the class of $(0,1,0)$.
--
--   This records that the generic point of the projective model of an elliptic Weierstrass curve is not a $2$-torsion point: doubling its chart-evaluated projective coordinate triple does not give the point at infinity. It is the input to [`WeierstrassProjModel.kw_ev_genericPoint_not_two_torsion`](thm.html#WeierstrassProjModel.kw_ev_genericPoint_not_two_torsion), which converts the chart statement into the assertion $2\,e(\eta)\neq 0$ in the group of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_ev_genericPoint_chartFactor_addMap_self_ne_zeroClass.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

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

theorem WeierstrassProjModel.kw_ev_genericPoint_chartFactor_addMap_self_ne_zeroClass
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    haveI : IsIntegral (projModelCR W.toProjective) :=
      GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
    letI : Algebra R (projModelCR W.toProjective).functionField :=
      (Spec.preimage ((projModelCR W.toProjective).fromSpecStalk
        (genericPoint (projModelCR W.toProjective)) ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R (projModelCR W.toProjective).functionField W.Δ ≠ 0 :=
      (W.isUnit_Δ.map _).ne_zero
    ∃ (i : Fin 3) (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] (projModelCR W.toProjective).functionField),
      (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
        = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i
      ∧ (kw_lrApt_WF W (projModelCR W.toProjective).functionField).addMap
          ⟦kw_lrApt_chartEval W (projModelCR W.toProjective).functionField i ψ⟧
          ⟦kw_lrApt_chartEval W (projModelCR W.toProjective).functionField i ψ⟧
        ≠ ⟦![(0 : (projModelCR W.toProjective).functionField), 1, 0]⟧ := by sorry
