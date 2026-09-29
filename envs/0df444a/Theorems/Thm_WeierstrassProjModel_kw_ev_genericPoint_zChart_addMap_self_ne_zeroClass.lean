-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass
-- name    : WeierstrassProjModel.kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/14c9c297-faf3-585a-8142-02dc872ecf1f
-- title:
--   Doubling the generic Z-chart point avoids [0:1:0]
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ whose discriminant is a unit (`W.IsElliptic`). Write $E = \mathrm{Proj}$ of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(\text{the Weierstrass cubic of } W.\mathrm{toProjective})$, graded by the images of the homogeneous submodules, with its structure morphism to $\mathrm{Spec}\,R$; this morphism is smooth of relative dimension $1$ and geometrically integral, so $E$ is integral and has a function field $K = E.\mathrm{functionField}$, which is made an $R$-algebra by the ring map underlying the composite of $E.\mathrm{fromSpecStalk}$ at the generic point with the structure morphism. The statement records that $\Delta_W$ has nonzero image in $K$, $\Delta_W$ being a unit. The assertion is: for every $R$-algebra homomorphism $\psi$ from the homogeneous localisation away from the class of $X_2$ into $K$ such that the canonical morphism $E.\mathrm{fromSpecStalk}$ at the generic point factors as $\mathrm{Spec}(\psi)$ followed by the $i = 2$ chart inclusion of the affine open cover of $E$, the projective addition map of $(W \otimes_R K).\mathrm{toProjective}$, applied to the class of the triple $k \mapsto \psi(\mathrm{gen}\,2\,k)$ with itself, is not the class of $![0,1,0]$.
--
--   This says that the tautological point of the generic fibre obtained from a factorisation of the generic-point inclusion through the $Z$-chart is not $2$-torsion: its double is not the point at infinity, equivalently $2y + a_1 x + a_3 \neq 0$ in the function field. It is the $Z$-chart case used by [`WeierstrassProjModel.kw_ev_genericPoint_chartFactor_addMap_self_ne_zeroClass`](thm.html#WeierstrassProjModel.kw_ev_genericPoint_chartFactor_addMap_self_ne_zeroClass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass.lean

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

theorem WeierstrassProjModel.kw_ev_genericPoint_zChart_addMap_self_ne_zeroClass
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
    ∀ (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)) →ₐ[R] (projModelCR W.toProjective).functionField),
      (projModelCR W.toProjective).fromSpecStalk (genericPoint (projModelCR W.toProjective))
        = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3)
      → (kw_lrApt_WF W (projModelCR W.toProjective).functionField).addMap
          ⟦kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ⟧
          ⟦kw_lrApt_chartEval W (projModelCR W.toProjective).functionField (2 : Fin 3) ψ⟧
        ≠ ⟦![(0 : (projModelCR W.toProjective).functionField), 1, 0]⟧ := by sorry
