-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrThird_u3_class_eq_addMap_of_delta_ne_zero
-- name    : WeierstrassProjModel.kw_lrThird_u3_class_eq_addMap_of_delta_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/116012a1-e75d-5ad0-93b4-fe9808c1fb15
-- title:
--   Third-law chart factorisation computes projective addition over F
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$; write $\mathcal A$ for the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(W_{\mathrm{proj}})$ with the grading induced from the homogeneous submodules, and for $m \in \mathrm{Fin}\,3$ let $\mathcal A_m$ be the homogeneous localisation `HomogeneousLocalization.Away` of this grading at the class of $X_m$, an $R$-algebra via degree zero. Let $F$ be a field and an $R$-algebra in which the discriminant does not vanish, i.e. $\mathrm{algebraMap}\,R\,F\,(W.\Delta) \neq 0$. Given indices $i, j, k, k'$ and $R$-algebra maps $\psi_i \colon \mathcal A_i \to F$, $\psi_j \colon \mathcal A_j \to F$, $\psi_{k'} \colon \mathcal A_{k'} \to F$, assume that the image of `kw_lrThird_u₃ W i j k` under the product map $\mathcal A_i \otimes_R \mathcal A_j \to F$ determined by $\psi_i$ and $\psi_j$ is a unit, so that this product map extends to the localisation away from that element, and assume that the resulting morphism $\mathrm{Spec}\,F \to \mathrm{Spec}$ of that localisation followed by `kw_lrThird_toE₃ W i j k` coincides with $\mathrm{Spec}\,\psi_{k'}$ followed by the $k'$-th map of the affine open cover `projModelAffineOpenCoverCR` of the projective model. Then, for the base-changed curve $(W \otimes_R F)$ viewed as a projective Weierstrass curve, the point class of the triple $m \mapsto \psi_{k'}(\mathrm{gen}\,k'\,m)$ equals `addMap` applied to the classes of $m \mapsto \psi_i(\mathrm{gen}\,i\,m)$ and $m \mapsto \psi_j(\mathrm{gen}\,j\,m)$.
--
--   This identifies the third (Bosma–Lenstra) addition law on the projective model, read on a single chart, with Mathlib's projective addition of point classes on the base-changed curve: whenever an $F$-point of the chart $i$ times chart $j$ product has invertible $k$-th third-law coordinate and its image under the third-law chart morphism lands in the chart $k'$, the coordinates read off there represent the sum of the two input classes. It feeds the compatibility statement [`WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain`](thm.html#WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrThird_u3_class_eq_addMap_of_delta_ne_zero.lean

import Definitions.Def_WeierstrassCurve_ProjModel_ThirdLawCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.kw_lrThird_u3_class_eq_addMap_of_delta_ne_zero.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (hΔ : algebraMap R F W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (ψⱼ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X j : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (k : Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrThird_u₃ W i j k)))
    (k' : Fin 3) (ψₖ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k' : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrThird_u₃ W i j k)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrThird_toE₃ W i j k
        = Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k') :
    (⟦kw_lrApt_chartEval W F k' ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = (kw_lrApt_WF W F).addMap ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by sorry
