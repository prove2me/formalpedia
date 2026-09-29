-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_mul_zeroSect
-- name    : WeierstrassProjModel.addMorphism_mul_zeroSect
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/e6dec05e-f086-58e6-bafe-515bffbdcfe2
-- title:
--   Right unit law for the glued addition morphism
-- statement:
--   Let $R$ be a commutative ring that is a Noetherian integral domain and let $W$ be a Weierstrass curve over $R$. Write $E = \mathrm{Proj}$ of the graded ring $R[X_0,X_1,X_2]$ modulo the homogeneous ideal of the projective Weierstrass cubic of $W$, with its induced grading, and let $\pi$ be the structure morphism `projModelStrCR W.toProjective` to $\mathrm{Spec}\,R$, namely `Proj.toSpecZero` followed by the map induced by $R \to$ (degree-zero part). Assume $\pi$ is smooth and geometrically integral, that the discriminant $W.\Delta$ is a unit of $R$, and that the three gluing hypotheses hold: `hcov`, asserting that for all $i,j$ the six elements $\mathrm{kw\_lrSixU}\,W\,i\,j$ (the chart and symmetric-chart $u$-elements) generate the unit ideal of $(\mathcal{A}_i)\otimes_R(\mathcal{A}_j)$; `hcompat`, asserting that on each fibre product of two of the six localisation spectra the two induced morphisms to $E$ agree; and `houter`, asserting the analogous agreement of the per-chart morphisms on overlaps of the open cover of $\mathrm{pullback}\,\pi\,\pi$ by products of the affine charts. Let $m$ be the morphism $\mathrm{pullback}\,\pi\,\pi \to E$ glued from those per-chart morphisms, and let $o$ be the section of $\pi$ given by $\mathrm{Spec}$ of the ring map `kwYChartEval` followed by the affine chart inclusion at $X_1$ (the point $[0:1:0]$), bundled with the identity $o \circ \pi = \mathrm{id}$ over $\mathrm{Spec}\,R$. Then the morphism $E \to \mathrm{pullback}\,\pi\,\pi$ with components $\mathrm{id}_E$ and $\pi$ followed by $o$, composed with $m$, equals $\mathrm{id}_E$. The compatibility condition required by `pullback.lift` is discharged inside the statement from the section property of $o$ by the category axioms.
--
--   This is the right unit law, $x + 0 = x$, for the addition morphism obtained by gluing the chord and symmetric addition laws on the projective Weierstrass model over a Noetherian domain with unit discriminant. It is one of the group-law axioms fed into [`WeierstrassProjModel.relativeGroupLaw_exists_of_gluing`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists_of_gluing), which packages the glued morphism as a relative group law on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_mul_zeroSect.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_mul_zeroSect.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback.lift (𝟙 (projModelCR W.toProjective)) (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1)
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, Category.id_comp])
      ≫ kw_lrAddMorphism W hcov hcompat houter = 𝟙 (projModelCR W.toProjective) := by sorry
