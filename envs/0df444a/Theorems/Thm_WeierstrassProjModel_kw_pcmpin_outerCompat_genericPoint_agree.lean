-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_pcmpin_outerCompat_genericPoint_agree
-- name    : WeierstrassProjModel.kw_pcmpin_outerCompat_genericPoint_agree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c028a322-62d8-579f-81da-d2f1dbd16cc4
-- title:
--   Pinned per-chart addition maps agree at generic points of overlaps
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ which is elliptic. Write $\mathcal A_i$ for the degree-zero homogeneous localisation of the graded quotient $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(W.\mathrm{toProjective}.\mathrm{polynomial})$, graded by the images of the homogeneous submodules, away from the class of $X_i$, so that the projective model is $E=\mathrm{Proj}$ of that grading. Assume given a family $\mathrm{pcm}_{i,j}\colon \operatorname{Spec}(\mathcal A_i\otimes_R\mathcal A_j)\to E$, $i,j\in\mathrm{Fin}\,3$, together with the pinning hypothesis that for all $i,j$ and every index $l\in \mathrm{Fin}\,3\sqcup\mathrm{Fin}\,3$ the morphism $\operatorname{Spec}$ of the localisation map $\mathcal A_i\otimes_R\mathcal A_j\to (\mathcal A_i\otimes_R\mathcal A_j)_{u_l}$, followed by $\mathrm{pcm}_{i,j}$, equals the explicit morphism `kw_lrSixU_toE W i j l` to $E$ built from the corresponding chart or symmetric-chart ring homomorphism and the affine inclusion `Proj.awayι` at the degree-one element $X_k$; here $u_l$ runs over the six elements `kw_lrSixU W i j`. Let $ij,ij'$ be two indices of the open cover of $E\times_{\operatorname{Spec}R}E$ obtained from products of the standard affine charts, and assume the overlap, i.e. the pullback of the two cover maps, is an integral scheme. Then the two composites obtained from the morphism out of the spectrum of the stalk at the generic point of this overlap, followed respectively by the first projection, the chart identification $(E\times E)$-chart $\cong\operatorname{Spec}(\mathcal A_{ij.1}\otimes_R\mathcal A_{ij.2})$ and $\mathrm{pcm}_{ij.1,ij.2}$, and by the second projection, the chart identification for $ij'$ and $\mathrm{pcm}_{ij'.1,ij'.2}$, are equal.
--
--   This is the generic-fibre agreement step in the gluing of the per-chart addition morphisms on the Weierstrass projective model into a single addition $E\times_{\operatorname{Spec}R}E\to E$: on an integral overlap of two product charts the two pinned candidates become equal after pulling back to the spectrum of the function field. It is used by [`WeierstrassProjModel.kw_pcmpin_outerCompat_dense_witness`](thm.html#WeierstrassProjModel.kw_pcmpin_outerCompat_dense_witness), which upgrades the generic-point equality to a scheme-theoretically dominant witness for the compatibility of the two charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_pcmpin_outerCompat_genericPoint_agree.lean

import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

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

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.kw_pcmpin_outerCompat_genericPoint_agree
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3), Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l)
    (ij ij' : Fin 3 × Fin 3)
    [IsIntegral ↑(pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                           ((kwProjPullbackOpenCoverCR R W.toProjective).f ij'))] :
    (pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
              ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')).fromSpecStalk
        (genericPoint _)
        ≫ pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                       ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2
      = (pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                  ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')).fromSpecStalk
          (genericPoint _)
        ≫ pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                       ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ (kwProjPullbackChartIsoCR R W.toProjective ij'.1 ij'.2).hom ≫ pcm ij'.1 ij'.2 := by sorry
