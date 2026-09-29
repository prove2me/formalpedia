-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_not_two_torsion
-- name    : WeierstrassProjModel.kw_ev_genericPoint_not_two_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/02b706d6-f939-5172-8c0c-3f1f68a7a6f9
-- title:
--   Generic-point evaluation is not 2-torsion
-- statement:
--   Let $R$ be a commutative ring that is a Noetherian integral domain, and let $W$ be a Weierstrass curve over $R$ whose discriminant $\Delta$ is a unit. Write $E =$ `projModelCR W.toProjective` for the $\mathrm{Proj}$ of the graded quotient of $R[X_0,X_1,X_2]$ by the homogeneous Weierstrass ideal, with structure morphism `projModelStrCR W.toProjective` to $\operatorname{Spec} R$ obtained from `Proj.toSpecZero` followed by $\operatorname{Spec}$ of $R \to$ (degree-zero part). The statement installs, as part of its formulation, smoothness of this structure morphism (from relative dimension $1$), geometric integrality (via the identification of its base changes with the $\mathrm{Proj}$ models of the base-changed curve), hence integrality of $E$; so the function field $F$ of $E$ is available, and it is made an $R$-algebra through the morphism $\operatorname{Spec} F \to E \to \operatorname{Spec} R$ given by `fromSpecStalk` at the generic point. Since $\Delta$ is a unit, its image in $F$ is nonzero. Let $e$ be the point-evaluation map supplied by the last component of `exists_pointEval` for the field $F$, sending $\operatorname{Spec} R$-morphisms $\operatorname{Spec} F \to E$ to $F$-points of the Weierstrass curve. The conclusion is that $2 \cdot e(\eta) \neq 0$, where $\eta$ is the tautological $F$-point `fromSpecStalk` at the generic point, viewed as a morphism over $\operatorname{Spec} R$.
--
--   This says that the tautological function-field point of the projective Weierstrass model is not $2$-torsion, equivalently $e(\eta) \neq -e(\eta)$. It is used in [`WeierstrassProjModel.pin_addMorphism_negMor_mul`](thm.html#WeierstrassProjModel.pin_addMorphism_negMor_mul), where a density argument must be evaluated at the off-diagonal pair $(-\eta, \eta)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_ev_genericPoint_not_two_torsion.lean

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

theorem WeierstrassProjModel.kw_ev_genericPoint_not_two_torsion
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
    (2 : ℤ) • (exists_pointEval W (projModelCR W.toProjective).functionField hΔF).2.2.choose
        ⟨(projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective)),
          by
            show (projModelCR W.toProjective).fromSpecStalk _ ≫ projModelStrCR W.toProjective
              = Spec.map (CommRingCat.ofHom (algebraMap R (projModelCR W.toProjective).functionField))
            rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
      ≠ 0 := by sorry
