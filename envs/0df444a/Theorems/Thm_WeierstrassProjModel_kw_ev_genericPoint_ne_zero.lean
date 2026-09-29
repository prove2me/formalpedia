-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_ne_zero
-- name    : WeierstrassProjModel.kw_ev_genericPoint_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/40cb48e5-ae9d-5f54-b3d1-a72d5a19571e
-- title:
--   The generic point is a nonzero point of the model
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ which is elliptic (so its discriminant $\Delta$ is a unit). Write $E = \operatorname{Proj}$ of the graded quotient of $R[X_0,X_1,X_2]$ by the homogeneous ideal of the projective Weierstrass cubic of $W$, with structure morphism to $\operatorname{Spec} R$ given by `projModelStrCR`. The statement first installs, as part of its own formulation, the facts that this structure morphism is smooth (being smooth of relative dimension $1$, by `projModelStrCR_smoothOfRelativeDimension_one`) and geometrically integral (via `kw_hgi_geometricallyIntegral_of_baseChangeIso` applied to the base-change isomorphism `projModel_pullback_iso_baseChange`), hence that $E$ is an integral scheme; consequently $E$ has a generic point and a function field $F = K(E)$, which is made an $R$-algebra by the ring map underlying the composite of $E$'s canonical morphism $\operatorname{Spec}\mathcal{O}_{E,\eta} = \operatorname{Spec} F \to E$ followed by the structure morphism. Since $\Delta$ is a unit in $R$, its image in $F$ is nonzero, which is the hypothesis required by `exists_pointEval`. The conclusion asserts that the evaluation map chosen from `exists_pointEval` for the field $F$, applied to the tautological $F$-point of $E$ over $\operatorname{Spec} R$ — namely $\eta \colon \operatorname{Spec} F \to E$, whose compatibility with the structure morphism holds by construction of the $R$-algebra structure on $F$ — takes a value different from $0$.
--
--   This records that the tautological function-field point of the projective Weierstrass model is not the identity element, i.e. the generic point does not lie on the zero section. It supplies the off-diagonal witness for the pairs $(O,\eta)$ and $(\eta,O)$ used in [`WeierstrassProjModel.pin_addMorphism_zeroSect_mul`](thm.html#WeierstrassProjModel.pin_addMorphism_zeroSect_mul) and [`WeierstrassProjModel.pin_addMorphism_mul_zeroSect`](thm.html#WeierstrassProjModel.pin_addMorphism_mul_zeroSect).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_ev_genericPoint_ne_zero.lean

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

theorem WeierstrassProjModel.kw_ev_genericPoint_ne_zero
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
    (exists_pointEval W (projModelCR W.toProjective).functionField hΔF).2.2.choose
        ⟨(projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective)),
          by
            show (projModelCR W.toProjective).fromSpecStalk _ ≫ projModelStrCR W.toProjective
              = Spec.map (CommRingCat.ofHom (algebraMap R (projModelCR W.toProjective).functionField))
            rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
      ≠ 0 := by sorry
