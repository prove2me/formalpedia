-- Prove2me | Theorems.Thm_WeierstrassProjModel_sixU_toE_over
-- name    : WeierstrassProjModel.sixU_toE_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/dcc57d89-1c5d-580b-b48f-c3d9af8e2040
-- title:
--   The six addition-law chart morphisms are morphisms over Spec R
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$. Write $E = \operatorname{Proj}$ of the grading `projModelGradingCR W.toProjective`, i.e. of the grading on $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, R)/(F)$ obtained by pushing the homogeneous submodules forward along the quotient map, where $F$ is the Weierstrass cubic of `W.toProjective` (the ideal it spans being homogeneous), and let $\mathcal A_k = \mathrm{HomogeneousLocalization.Away}$ of that grading at the class of $X_k$, so that $\operatorname{Spec}\mathcal A_k$ is the $k$-th standard chart. The structure morphism `projModelStrCR W.toProjective` is `Proj.toSpecZero` followed by $\operatorname{Spec}$ of the algebra map $R \to$ (degree-zero part). Fix $i, j \in \mathrm{Fin}\,3$ and an index $l \in \mathrm{Fin}\,3 \oplus \mathrm{Fin}\,3$, and let $u_l =$ `kw_lrSixU W i j l` $\in \mathcal A_i \otimes_R \mathcal A_j$, namely `kw_lrChart_u W i j k` for $l = \mathrm{inl}\,k$ and `kw_lrSymChart_u W i j k` for $l = \mathrm{inr}\,k$. On $\operatorname{Spec}$ of $\mathrm{Localization.Away}\,u_l$ two morphisms are given: `kw_lrSixU_toE W i j l`, which for $l = \mathrm{inl}\,k$ is $\operatorname{Spec}$ of `kw_lrChart_tensor W i j k` followed by the affine open immersion `Proj.awayι` at the degree-one element $\overline{X_k}$ (and likewise with `kw_lrSymChart_tensor` for $l = \mathrm{inr}\,k$), and `kw_lrSixU_locMap W i j l`, which is $\operatorname{Spec}$ of the localisation map $\mathcal A_i \otimes_R \mathcal A_j \to \mathrm{Localization.Away}\,u_l$. The theorem asserts that `kw_lrSixU_toE W i j l` followed by `projModelStrCR W.toProjective` equals `kw_lrSixU_locMap W i j l` followed by $\operatorname{Spec}$ of the structure map $R \to \mathcal A_i \otimes_R \mathcal A_j$.
--
--   This records that each of the six addition-law loci on the chart $\operatorname{Spec}(\mathcal A_i \otimes_R \mathcal A_j)$ of $E \times_R E$ maps to the projective Weierstrass model by a morphism over the base $\operatorname{Spec} R$, which is what allows these local pieces to be glued into an addition morphism over $R$. It is used in the construction of the chart-wise addition morphism and its compatibility statements, such as [`WeierstrassProjModel.exists_perChart_addMorphism_of_nineGlue_compat`](thm.html#WeierstrassProjModel.exists_perChart_addMorphism_of_nineGlue_compat) and [`WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain`](thm.html#WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_sixU_toE_over.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.sixU_toE_over.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    kw_lrSixU_toE W i j l ≫ projModelStrCR W.toProjective
      = kw_lrSixU_locMap W i j l
          ≫ Spec.map (CommRingCat.ofHom (algebraMap R
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (MvPolynomial.X i : MvPolynomial (Fin 3) R))
                ⊗[R] HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (MvPolynomial.X j : MvPolynomial (Fin 3) R))))) := by sorry
