-- Prove2me | Theorems.Thm_WeierstrassProjModel_perChart_addMorphism_pin_outerCompat
-- name    : WeierstrassProjModel.perChart_addMorphism_pin_outerCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/47392214-395e-59d8-8bd5-c418b64033a1
-- title:
--   Overlap compatibility of pinned per-chart addition morphisms
-- statement:
--   Let $R$ be a Noetherian integral domain and $W$ a Weierstrass curve over $R$ that is elliptic. Write $E = \operatorname{Proj}$ of the grading induced on $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(F_W)$, $F_W$ the homogeneous Weierstrass cubic of $W$, and for $i \in \mathrm{Fin}\,3$ let $\mathcal{A}_i$ be the degree-zero homogeneous localisation of that graded quotient away from the class of $X_i$, an $R$-algebra via the degree-zero part; $\pi =$ `projModelStrCR` is the structure morphism $E \to \operatorname{Spec} R$. Assume given, for every pair $(i,j)$, a morphism $\mathrm{pcm}_{ij} \colon \operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j) \to E$, and assume the pinning hypothesis that for all $i,j$ and every $l \in \mathrm{Fin}\,3 \sqcup \mathrm{Fin}\,3$ the composite of the localisation morphism $\operatorname{Spec}\big(\mathrm{Away}(u_l)\big) \to \operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$ with $\mathrm{pcm}_{ij}$ equals `kw_lrSixU_toE W i j l`, where $u_l$ runs over the six Lange–Ruppert units `kw_lrSixU W i j` and `kw_lrSixU_toE` is the corresponding map to $E$ through the away-chart immersion $\operatorname{Proj.awayι}$. Then for any two indices $ij, ij' \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$ of the nine-chart open cover `kwProjPullbackOpenCoverCR` of $E \times_{\operatorname{Spec} R} E$ (the left–right product of the three away charts of $E$ with itself), the two morphisms obtained on the overlap of the $ij$- and $ij'$-charts agree: the first projection of the pullback of the two cover inclusions, followed by the isomorphism `kwProjPullbackChartIsoCR` identifying the $ij$-chart with $\operatorname{Spec}(\mathcal{A}_{ij_1} \otimes_R \mathcal{A}_{ij_2})$ and then $\mathrm{pcm}_{ij_1 ij_2}$, equals the second projection followed by the corresponding composite for $ij'$.
--
--   This is the overlap-compatibility half of the data needed to glue the nine chart-wise candidate addition morphisms on $E \times_{\operatorname{Spec} R} E$ into a single morphism $E \times_{\operatorname{Spec} R} E \to E$; it is used by `exists_addMorphism_of_perChart_addMorphism_pin`, the companion being the over-$\operatorname{Spec} R$ compatibility `perChart_addMorphism_pin_over`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_perChart_addMorphism_pin_outerCompat.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

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

theorem WeierstrassProjModel.perChart_addMorphism_pin_outerCompat
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3),
      Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l)
    (ij ij' : Fin 3 × Fin 3) :
    pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                 ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2
      = pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                     ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ (kwProjPullbackChartIsoCR R W.toProjective ij'.1 ij'.2).hom ≫ pcm ij'.1 ij'.2 := by sorry
