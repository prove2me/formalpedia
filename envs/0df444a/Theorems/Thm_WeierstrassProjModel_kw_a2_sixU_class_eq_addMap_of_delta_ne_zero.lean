-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
-- name    : WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d4ee42f0-cb2e-58ee-a890-ad9bffb79b7f
-- title:
--   Chart factorisation of the six-U locus computes addMap
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $F$ a field which is an $R$-algebra such that the image of the discriminant $W.\Delta$ in $F$ is non-zero. Write $\mathcal{A}$ for the grading on $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(\text{the Weierstrass cubic of } W.\mathrm{toProjective})$ obtained by pushing forward the homogeneous submodules, and for $i : \mathrm{Fin}\,3$ let the $i$-th chart ring be the homogeneous localisation away from the class of $X_i$, an $R$-algebra via degree zero. Given chart indices $i, j$ and $R$-algebra maps $\psi_i, \psi_j$ from the $i$-th and $j$-th chart rings to $F$, an index $l : \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$ (selecting, on the left summand at $k$, the element `kw_lrChart_u W i j k` of $\mathcal{A}_i \otimes_R \mathcal{A}_j$ coming from the addition vector, and on the right summand the symmetric, doubling, analogue), assume that the image of `kw_lrSixU W i j l` under the product map $\psi_i \otimes \psi_j : \mathcal{A}_i \otimes_R \mathcal{A}_j \to F$ is a unit. Given further $k : \mathrm{Fin}\,3$ and an $R$-algebra map $\psi_k$ from the $k$-th chart ring to $F$, assume that $\mathrm{Spec}$ of the induced map from the localisation away from `kw_lrSixU W i j l`, followed by `kw_lrSixU_toE W i j l` into the projective model, coincides with $\mathrm{Spec}(\psi_k)$ followed by the $k$-th map of the affine open cover `projModelAffineOpenCoverCR`. Then in $\mathrm{PointClass}\,F$ the class of the triple $(\psi_k(\mathrm{gen}\,k\,0), \psi_k(\mathrm{gen}\,k\,1), \psi_k(\mathrm{gen}\,k\,2))$ equals $\mathrm{addMap}$ for $(W.\mathrm{baseChange}\,F).\mathrm{toProjective}$ applied to the classes of the corresponding triples for $\psi_i$ and $\psi_j$.
--
--   This identifies the scheme-theoretic chord-and-tangent addition on the projective Weierstrass model, read through the six standard addition and doubling charts, with the explicit $\mathrm{addMap}$ formulae on projective point classes, under the assumption that the discriminant is invertible in $F$. It is the per-locus, unit-local step used by the multiplicativity and chart-independence results for the evaluation maps of the projective model, such as [`WeierstrassProjModel.kw_a2_map_mul_of_delta_ne_zero`](thm.html#WeierstrassProjModel.kw_a2_map_mul_of_delta_ne_zero) and [`WeierstrassProjModel.kw_ev_triple_projections_chartFactor_pointClass_indep`](thm.html#WeierstrassProjModel.kw_ev_triple_projections_chartFactor_pointClass_indep); the proof cites the polynomial identities `kw_a2_checks_addXYZ_crossXZ` and `kw_a2_checks_crossYZ` relating the addition and symmetric vectors to $\mathrm{addX}$, $\mathrm{addY}$, $\mathrm{addZ}$ and the doubling coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_a2_sixU_class_eq_addMap_of_delta_ne_zero.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.kw_a2_sixU_class_eq_addMap_of_delta_ne_zero.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (hΔ : algebraMap R F W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (ψⱼ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X j : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (l : Fin 3 ⊕ Fin 3)
    (hu : IsUnit ((Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l)))
    (k : Fin 3) (ψₖ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : Spec.map (CommRingCat.ofHom
            (IsLocalization.Away.lift (kw_lrSixU W i j l)
              (g := (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom) hu))
          ≫ kw_lrSixU_toE W i j l
        = Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = (kw_lrApt_WF W F).addMap ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ := by sorry
