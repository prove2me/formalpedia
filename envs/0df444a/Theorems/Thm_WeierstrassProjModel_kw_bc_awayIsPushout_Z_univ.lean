-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_bc_awayIsPushout_Z_univ
-- name    : WeierstrassProjModel.kw_bc_awayIsPushout_Z_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d3d11746-6b16-56b1-a9ff-bb7d4ae6fdba
-- title:
--   Base change is cartesian on the X₂-chart
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve over $R$, and let $K$ be a commutative ring with an $R$-algebra structure, with structure map $\mathrm{algebraMap}\,R\,K$. Consider the graded quotient rings $\mathcal B_R = \mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(F_W)$ and $\mathcal B_K = \mathrm{MvPolynomial}(\mathrm{Fin}\,3,K)/(F_{W_K})$, where $F_W$ is the projective Weierstrass polynomial of $W$, $W_K$ is the base change of $W$ along $R \to K$, and the degree-$n$ piece of either quotient is the image of the degree-$n$ homogeneous polynomials under the quotient map. The statement first introduces the graded ring homomorphism $\psi \colon \mathcal B_R \to \mathcal B_K$ induced on quotients by applying $\mathrm{algebraMap}\,R\,K$ to coefficients; this is well defined because the image of $(F_W)$ generates $(F_{W_K})$, and it preserves degrees. The assertion is that the square of affine schemes with top edge $\operatorname{Spec}$ of the induced map of degree-zero homogeneous localizations $\mathrm{Away}(\mathcal B_R, \overline{X_2}) \to \mathrm{Away}(\mathcal B_K, \psi(\overline{X_2}))$, left and right edges the structure morphisms of these two chart rings over $\operatorname{Spec} K$ and $\operatorname{Spec} R$ respectively (obtained from $\mathrm{fromZeroRingHom}$ precomposed with the relevant algebra maps), and bottom edge $\operatorname{Spec}(\mathrm{algebraMap}\,R\,K)$, is a pullback square of schemes.
--
--   This is the affine-local input to base change for the projective Weierstrass model: the degree-zero away-chart $D_+(X_2)$ of the base-changed model is the base change of the corresponding chart, equivalently $K \otimes_R (\mathcal B_R)_{(X_2)} \cong (\mathcal B_K)_{(X_2)}$. It is used by [`WeierstrassProjModel.projModel_isPullback_baseChange`](thm.html#WeierstrassProjModel.projModel_isPullback_baseChange) and [`WeierstrassProjModel.projModel_isPullback_baseChange_ring`](thm.html#WeierstrassProjModel.projModel_isPullback_baseChange_ring), and by [`WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom`](thm.html#WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_bc_awayIsPushout_Z_univ.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.kw_bc_awayIsPushout_Z_univ {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (K : Type u) [CommRing K] [Algebra R K] :
    let ψ : projModelGradingCR W.toProjective →+*ᵍ
        projModelGradingCR (W.map (algebraMap R K)).toProjective :=
      { toRingHom := Ideal.quotientMap _ (MvPolynomial.map (algebraMap R K)) <| by
          rw [projModelHomogeneousIdealCR_toIdeal, projModelHomogeneousIdealCR_toIdeal]
          have h : (Ideal.span {W.toProjective.polynomial}).map
                (MvPolynomial.map (algebraMap R K))
              = Ideal.span {(W.map (algebraMap R K)).toProjective.polynomial} := by
            rw [Ideal.map_span, Set.image_singleton,
              WeierstrassCurve.Projective.map_polynomial]
          rw [← h]
          exact Ideal.le_comap_map,
        map_mem := by
          rintro n _ ⟨p, hp, rfl⟩
          exact mk_mem_quotGradingSubmodule _ _
            ((mem_homogeneousSubmodule _ _).mpr
              (((mem_homogeneousSubmodule _ _).mp hp).map (algebraMap R K))) }
    IsPullback
      (Spec.map (CommRingCat.ofHom (Away.map ψ
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (X 2 : MvPolynomial (Fin 3) R)))))
      (Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom (projModelGradingCR (W.map (algebraMap R K)).toProjective)
            (Submonoid.powers (ψ (Ideal.Quotient.mk _
              (X 2 : MvPolynomial (Fin 3) R))))).comp
          (algebraMap K ↥(projModelGradingCR (W.map (algebraMap R K)).toProjective 0)))))
      (Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom (projModelGradingCR W.toProjective)
            (Submonoid.powers (Ideal.Quotient.mk _
              (X 2 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R ↥(projModelGradingCR W.toProjective 0)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by sorry
