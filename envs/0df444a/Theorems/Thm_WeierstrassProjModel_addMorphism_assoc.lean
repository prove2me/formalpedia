-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_assoc
-- name    : WeierstrassProjModel.addMorphism_assoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/b84e42d4-253d-5cb5-a613-d03d15cffa33
-- title:
--   Associativity of the glued addition morphism on Proj
-- statement:
--   Let $R$ be a Noetherian integral domain and $W$ a Weierstrass curve over $R$; write $\pi$ for `projModelStrCR W.toProjective`, the structure morphism from $\mathrm{Proj}$ of the quotient grading of the homogeneous coordinate ring of the projective Weierstrass model by its defining homogeneous ideal to $\operatorname{Spec} R$, obtained by composing `Proj.toSpecZero` with the map induced by $R \to \mathcal{A}_0$. Assume $\pi$ is smooth and geometrically integral, that $W.\Delta$ is a unit, and fix proofs of the three gluing hypotheses: `KwLRSixUCoverage`, that for all $i,j$ the six elements `kw_lrSixU W i j` generate the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; `KwLRPerChartCompat`, that for all $i,j$ and all $l,l'$ the two maps `kw_lrSixU_toE` agree on the pullback of the corresponding localisation-away Spec maps; and `KwLROuterCompat`, that the morphisms `kw_lrOuter_toE` agree on all overlaps of the product open cover `kwProjPullbackOpenCoverCR` of $E \times_{\operatorname{Spec} R} E$. Let $m$ be the glued morphism `kw_lrAddMorphism W hcov hcompat houter` from that pullback to $E$, and assume $m \circ \pi$-compatibility: $\pi \circ m$ equals $\pi$ composed after the first projection. The conclusion asserts, on the triple pullback of $\pi \circ \mathrm{fst}$ against $\pi$, the equality of the two morphisms to $E$ given by $(P,Q,S) \mapsto m(m(P,Q),S)$ and $(P,Q,S) \mapsto m(P,m(Q,S))$, the required pairing conditions being supplied inside the statement from the hypothesis on $\pi \circ m$ and the pullback conditions.
--
--   This is the associativity axiom for the relative group law on the projective Weierstrass model, expressed scheme-theoretically for the morphism glued from the chord and symmetric addition laws on the product of affine charts. It is used by [`WeierstrassProjModel.relativeGroupLaw_exists_of_gluing`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists_of_gluing), which assembles the group-law axioms into the existence of a relative group structure on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_assoc.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_assoc.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
    (hm : kw_lrAddMorphism W hcov hcompat houter ≫ projModelStrCR W.toProjective
      = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) :
    pullback.lift
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ kw_lrAddMorphism W hcov hcompat houter)
        (pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (by rw [Category.assoc, hm]; exact pullback.condition)
      ≫ kw_lrAddMorphism W hcov hcompat houter
    = pullback.lift
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (pullback.lift
            (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
                ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
              ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
            (pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
                ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
            ((Category.assoc _ _ _).trans
              ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition))
          ≫ kw_lrAddMorphism W hcov hcompat houter)
        (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc]
            exact congrArg (_ ≫ ·) pullback.condition)
      ≫ kw_lrAddMorphism W hcov hcompat houter := by sorry
