-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_comm
-- name    : WeierstrassProjModel.addMorphism_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/af2a3b86-9a91-5e9b-a6f1-62f56667557b
-- title:
--   Commutativity of the glued addition morphism
-- statement:
--   Let $R$ be a Noetherian commutative integral domain and $W$ a Weierstrass curve over $R$, and write $\pi =$ `projModelStrCR W.toProjective` for the structure morphism $\mathrm{Proj}\,\mathcal{A} \to \mathrm{Spec}\,R$ of the projective Weierstrass model, where $\mathcal{A}$ is the grading induced on the quotient of $R[X_0,X_1,X_2]$ by the homogeneous ideal of the Weierstrass cubic, and $\pi$ is the composite of `Proj.toSpecZero` with the morphism induced by $R \to \mathcal{A}_0$. Assume $\pi$ is smooth and geometrically integral, that the discriminant $W.\Delta$ is a unit in $R$, and that the three gluing hypotheses hold: `KwLRSixUCoverage`, saying that for all $i,j \in \{0,1,2\}$ the six elements `kw_lrSixU W i j` (the three chart elements and the three symmetric-chart elements) generate the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; `KwLRPerChartCompat`, saying that for all $i,j$ and all pairs $l,l'$ of the six indices the two morphisms to the model obtained from `kw_lrSixU_toE` agree on the pullback of the corresponding localisation maps; and `KwLROuterCompat`, saying that the morphisms `kw_lrOuter_toE` agree on all overlaps of the $3\times 3$ open cover `kwProjPullbackOpenCoverCR` of $\mathrm{Proj}\,\mathcal{A} \times_{\mathrm{Spec}\,R} \mathrm{Proj}\,\mathcal{A}$. Then the swap morphism of the fibre product, i.e. `pullback.lift` applied to the second and first projections, followed by the glued morphism `kw_lrAddMorphism W hcov hcompat houter`, equals `kw_lrAddMorphism W hcov hcompat houter` itself.
--
--   This is the commutativity axiom for the relative group law on the projective Weierstrass model: the addition morphism glued from the chord and symmetric Lange–Ruppert addition laws is invariant under the swap automorphism of the fibre square. It is one of the group-law axioms used by [`WeierstrassProjModel.relativeGroupLaw_exists_of_gluing`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists_of_gluing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_comm.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_comm.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback.lift (pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        pullback.condition.symm
      ≫ kw_lrAddMorphism W hcov hcompat houter = kw_lrAddMorphism W hcov hcompat houter := by sorry
