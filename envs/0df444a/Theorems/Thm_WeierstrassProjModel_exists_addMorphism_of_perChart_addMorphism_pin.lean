-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin
-- name    : WeierstrassProjModel.exists_addMorphism_of_perChart_addMorphism_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/1e138514-0a27-5e91-b5a4-0c9aa9b19257
-- title:
--   Gluing pinned per-chart addition morphisms on E×_R E
-- statement:
--   Let $R$ be a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$ that is elliptic. Write $E = \mathrm{Proj}$ of the grading on $R[X_0,X_1,X_2]/(F)$ induced from the homogeneous submodules, where $F$ is the Weierstrass cubic of the projective model of $W$, write $\pi\colon E \to \operatorname{Spec} R$ for the structure morphism (`Proj.toSpecZero` followed by `Spec.map` of $R \to$ the degree-zero part), and write $\mathcal{A}_i$ for the homogeneous localisation of that graded ring away from the class of $X_i$. Suppose given, for each pair $i,j \in \{0,1,2\}$, a morphism $\mathrm{pcm}_{ij}\colon \operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j) \to E$, and suppose that for all $i,j$ and every index $l \in \mathrm{Fin}\,3 \sqcup \mathrm{Fin}\,3$ the canonical morphism $\operatorname{Spec}\bigl(\mathcal{A}_i\otimes_R\mathcal{A}_j\bigr)_{u_l} \to \operatorname{Spec}(\mathcal{A}_i\otimes_R\mathcal{A}_j)$, followed by $\mathrm{pcm}_{ij}$, equals the prescribed morphism `kw_lrSixU_toE` at $l$, namely `Spec.map` of the ring map $\mathcal{A}_k \to (\mathcal{A}_i\otimes_R\mathcal{A}_j)_{u_l}$ followed by the affine chart immersion $\mathrm{Proj}$-$\mathrm{away}$ at $X_k$. Then there is a morphism $m\colon E\times_{\operatorname{Spec} R} E \to E$ satisfying $m \circ \pi = \pi \circ \mathrm{pr}_1$ and such that, for each of the nine charts $(i,j)$ of the product open cover of the pullback, the chart's open immersion followed by $m$ equals the chart isomorphism onto $\operatorname{Spec}(\mathcal{A}_i\otimes_R\mathcal{A}_j)$ followed by $\mathrm{pcm}_{ij}$.
--
--   This is the gluing step in the construction of the relative group law on the projective Weierstrass model: nine chartwise addition morphisms, pinned on the six Lange–Ruppert localisations, are assembled into a single addition morphism $E\times_R E \to E$ lying over the base. It is used in the construction of the relative group law on $E$ and in the subsequent identification of its inversion and of its values on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_addMorphism_of_perChart_addMorphism_pin.lean

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

theorem WeierstrassProjModel.exists_addMorphism_of_perChart_addMorphism_pin
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3),
      Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l) :
    ∃ (m : pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ⟶ projModelCR W.toProjective)
      (_ : m ≫ projModelStrCR W.toProjective
            = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
                ≫ projModelStrCR W.toProjective),
      ∀ (ij : Fin 3 × Fin 3),
        (kwProjPullbackOpenCoverCR R W.toProjective).f ij ≫ m
          = (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom
              ≫ pcm ij.1 ij.2 := by sorry
